;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "physical-memory-utils" :dir :proof-utils)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;; ======================================================================

(defsection reasoning-about-page-tables
  :parents (proof-utilities)

  :short "Helper lemmas for reasoning about page-tables"

  :long "<p>The pattern followed to reason about the paging data
structures is described below.</p>

<ol>

  <li>

For each paging data structure walker, we define recognizers for valid
entries and functions to determine which addresses govern the
translation. E.g.:

<ul>
<li> @(see ia32e-la-to-pa-page-table-entry-validp) </li>
<li> @(see translation-governing-addresses-for-page-table) </li>
</ul>

We also define a top-level valid entry recognizer and
translation-governing address function that employs all the above
recognizers and functions:
<ul>
<li> @(see ia32e-la-to-pa-validp) </li>
<li> @(see translation-governing-addresses) </li>
</ul>

</li>

<li>

We prove rules about the return values of each of the walkers. E.g.:

<ul>
<li> @(see mv-nth-0-no-error-ia32e-la-to-pa-page-table) </li>
<li> @(see mv-nth-0-no-error-ia32e-la-to-pa-page-table-with-disjoint-!memi) </li>
<li> @(see mv-nth-0-no-error-ia32e-la-to-pa-page-table-with-disjoint-wm-low-64) </li>
<li> @(see mv-nth-1-no-error-ia32e-la-to-pa-page-table) </li>
<li> @(see mv-nth-1-no-error-ia32e-la-to-pa-page-table-with-disjoint-!memi) </li>
<li> @(see mv-nth-1-no-error-ia32e-la-to-pa-page-table-with-disjoint-wm-low-64) </li>
<li> @(see mv-nth-2-no-error-ia32e-la-to-pa-page-table) </li>
</ul>

</li>

<li>
We prove rules about reading an entry from an x86 state returned by
walking the same entry.  E.g.:

<ul>
<li> @(see rm-low-64-and-page-table) </li>
</ul>

</li>

<li>
We prove the commutativity of @('!memi') and the walker function,
given that @('!memi') writes to an address disjoint from the
translation-governing address.  E.g.:

<ul>
<li> disjoint-!memi-mv-nth-2-no-error-ia32e-la-to-pa-page-table </li>
</ul>

</li>

<li>
We prove rules about reading physical addresses disjoint from the
translation-governing addresses of the walker function.  E.g.:

<ul>
<li> @(see disjoint-!memi-mv-nth-2-no-error-ia32e-la-to-pa-page-table) </li>
<li> @(see disjoint-rm-low-64-mv-nth-2-no-error-ia32e-la-to-pa-page-table) </li>
</ul>

</li>

<li> We prove theorems that state that the validity of an entry is
preserved when writes are done to addresses disjoint from the
translation-governing addresses.  E.g.:

<ul>
<li> @(see page-table-entry-with-disjoint-!memi-still-valid-ia32e-la-to-pa-page-table) </li>
<li> @(see page-table-entry-with-disjoint-wm-low-64-still-valid-ia32e-la-to-pa-page-table) </li>
</ul>

</li>

<li> We prove theorems that state that the validity of an entry is
preserved with accessed and/or dirty bits are set.  E.g.:

<ul>
<li> @(see page-table-entry-with-accessed-bit-set-still-valid-ia32e-la-to-pa-page-table) </li>
<li> @(see page-table-entry-with-dirty-bit-set-still-valid-ia32e-la-to-pa-page-table) </li>
<li> @(see page-table-entry-with-accessed-and-dirty-bits-set-still-valid-ia32e-la-to-pa-page-table) </li>
</ul>

</li>

<li>
We prove theorems that state that the address returned by a walker
when reading an entry with the accessed and/or dirty bits set is the
same as the address returned by it without those bits being set.  E.g.:

<ul>
<li> @(see reading-entry-with-accessed-bit-set-ia32e-la-to-pa-page-table) </li>
<li> @(see reading-entry-with-dirty-bit-set-ia32e-la-to-pa-page-table) </li>
<li> @(see reading-entry-with-accessed-and-dirty-bits-set-ia32e-la-to-pa-page-table) </li>
</ul>

</li>

<li>
We prove that given that an entry @('e0') is valid w.r.t. an x86 state
@('x0'), another entry @('e1') in an x86 state @('x1') is valid if
some \"critical\" fields of those entries and sub-entries match.
E.g.:

<ul>
<li> @(see relating-validity-of-two-entries-in-two-x86-states-wrt-page-table-4K-pages) </li>
</ul>

</li>

<li>
Given that an entry @('e') is valid w.r.t. both permissions @('p0')
and @('p1'), we prove that the x86 state returned by walking @('e')
with @('p1') satisfies the recognizer of @('e') w.r.t. @('p0').

<ul>
<li> re-read-entry-still-valid-ia32e-la-to-pa-page-table </li>
</ul>
</li>

<li>
Given that an entry @('e') is valid w.r.t. both permissions @('p0')
and @('p1'), we prove that walking @('e') with @('p0') by reading the
x86 state returned by walking the same entry @('e') with @('p1')
returns an address that is the same as that obtained when @('e') is
walked with @('p0') by reading the initial x86 state.

<ul>
<li> @(see two-page-table-walks-ia32e-la-to-pa-page-table-same-addresses) </li>
</ul>

</li>

<li>
Given that an entry @('e') is valid w.r.t. @('p0') and x86 state
@('x'), @('e') is valid w.r.t. @('p1') and the same x86 state @('x'),
and the linear addresses @('lin-addr-1') and @('lin-addr-2') are
sufficiently different, we prove that walking @('e') with @('p0') by
reading the x86 state returned by walking @('e') with @('p1') on state
@('x') returns an address that is the same as that obtained when
@('e') is walked with @('p0') on @('x').

<ul>
<li> @(see two-page-table-walks-ia32e-la-to-pa-page-table-same-entry-different-addrs) </li>
</ul>

</li>


<li>
Given that an entry @('e0') is valid w.r.t. @('p0') and x86 state
@('x'), an entry @('e1') is valid w.r.t. @('p1') and the same x86
state @('x'), and the translation-governing addresses of @('e0') are
disjoint from that of @('e1'), we prove that walking @('e0') with
@('p0') by reading the x86 state returned by walking @('e1') with
@('p1') on state @('x') returns an address that is the same as that
obtained when @('e0') is walked with @('p0') on @('x').

<ul>
<li> @(see two-page-table-walks-ia32e-la-to-pa-page-table-different-entries) </li>
</ul>

</li>

<li>
Given that an entry @('e0') is valid w.r.t. @('p0') and x86 state
@('x'), an entry @('e1') is valid w.r.t. @('p1') and the same x86
state @('x'), and the translation-governing addresses of @('e0') are
disjoint from that of @('e1'), we prove that walking @('e1') with
@('p1') returns an x86 state where @('e0') still satisfies its
recognizer w.r.t. @('p0').

<ul>
<li> @(see validity-preserved-same-x86-state-disjoint-addresses-wrt-page-table) </li>
</ul>

</li>

</ol>
"
  )

;; I've got theorems (like two page walk theorem) about the following
;; three cases:

;; 1. same linear addresses, same translation-governing addresses (of
;;    course): this would correspond to the same physical addresses,
;;    of course.

;; 2. linear addresses differing only in their offsets, same
;;    translation-governing addresses (of course): this would
;;    correspond to the physical addresses being in the same page

;; 3. radically different linear addresses such that the
;;    translation-governing addresses are pairwise disjoint: physical
;;    addresses can be anything really.

;; ======================================================================

;; Some helper rules:

(encapsulate
 ()

 (defrule loghead-1-bool->bit-rule
   (equal (loghead 1 (bool->bit x))
	  (bool->bit x)))

 (encapsulate
  ()

  (local (include-book "arithmetic-5/top" :dir :system))

  (defrule low-3-bits-0-add-7-preserve-bound
    (implies (and (equal (loghead 3 x) 0)
		  (< x *mem-size-in-bytes*)
		  (integerp x))
	     (< (+ 7 x) *mem-size-in-bytes*))
    :in-theory (e/d* (loghead) ())))

 (defthm-usb rm-low-64-logand-logior-helper-1
   :hyp (and (n64p x)
	     (syntaxp (quotep n))
	     (natp n)
	     (<= n 64)
	     (equal m (- (1+ n))))
   :bound 64
   :concl (logior n (logand m x))
   :hints-l (("Goal" :in-theory (e/d () (force (force)))))
   :gen-type t
   :gen-linear t))

(in-theory (e/d* (low-3-bits-0-add-7-preserve-bound)
		 ()))

;; Disabling some expensive rules:

(local
 (in-theory (e/d ()
		 (ash-monotone-2
		  <-preserved-by-adding-<-*pseudo-page-size-in-bytes*-commuted
		  <-preserved-by-adding-<-*pseudo-page-size-in-bytes*))))

;; ======================================================================

;; For each paging data structure, we define recognizers for valid
;; entries and functions to determine which addresses govern the
;; translation.

;; Page Table:

(define ia32e-la-to-pa-page-table-entry-validp
  ((lin-addr             :type (signed-byte   #.*max-linear-address-size*))
   (page-table-base-addr :type (unsigned-byte #.*physical-address-size*))
   (u-s-acc              :type (unsigned-byte  1))
   (wp                   :type (unsigned-byte  1))
   (smep                 :type (unsigned-byte  1))
   (nxe                  :type (unsigned-byte  1))
   (r-w-x                :type (member  :r :w :x))
   (cpl                  :type (unsigned-byte  2))
   (x86))
  :parents (reasoning-about-page-tables)

  :enabled t
  :guard (and (canonical-address-p lin-addr)
	      (equal (loghead 12 page-table-base-addr) 0))
  :guard-hints (("Goal"
		 :in-theory (e/d (adding-7-to-shifted-bits)
				 (unsigned-byte-p
				  signed-byte-p
				  member-equal
				  not))))

  (let*
      ((page-table-entry-addr
	(page-table-entry-addr lin-addr page-table-base-addr))
       (entry (rm-low-64 page-table-entry-addr x86))
       (read-write (ia32e-page-tables-slice :r/w entry))
       (user-supervisor (ia32e-page-tables-slice :u/s entry))
       (execute-disable (ia32e-page-tables-slice :xd entry)))

    (and
     ;; 4K-aligned --- the base address is
     ;; the 40 bits wide address obtained
     ;; from the referencing PDE, shifted
     ;; left by 12.
     (equal (loghead 12 page-table-base-addr) 0)
     (equal (ia32e-page-tables-slice :p entry) 1)
     ;; The following three hyps state that the reserved
     ;; bits are unmodified.
     (equal
      (part-select entry :low
		   *physical-address-size* :high 62)
      0)
     (or
      (equal nxe 1)
      (equal (ia32e-pte-4K-page-slice :pte-xd entry) 0))
     ;; The following hyps state that access rights aren't
     ;; violated.

     (not
      (or
       ;; Read fault:
       (and (equal r-w-x :r)
	    (if (< cpl 3)
		nil
	      (equal user-supervisor 0)))
       ;; Write fault
       (and (equal r-w-x :w)
	    (if (< cpl 3)
		(and (equal wp 1)
		     (equal read-write 0))
	      (or (equal user-supervisor 0)
		  (equal read-write 0))))
       ;; Instruction fetch fault:
       (and (equal r-w-x :x)
	    (if (< cpl 3)
		(if (equal nxe 0)
		    (and (equal smep 1)
			 (equal u-s-acc 1)
			 (equal user-supervisor 1))
		  (if (equal smep 0)
		      (equal execute-disable 1)
		    (or (equal execute-disable 1)
			(and (equal u-s-acc 1)
			     (equal user-supervisor 1)))))
	      (or (equal user-supervisor 0)
		  (and (equal nxe 1)
		       (equal execute-disable 1))))))))))

(define translation-governing-addresses-for-page-table
  ((lin-addr             :type (signed-byte   #.*max-linear-address-size*))
   (page-table-base-addr :type (unsigned-byte #.*physical-address-size*))
   (x86))
  :parents (reasoning-about-page-tables)
  :guard (and (canonical-address-p lin-addr)
	      (equal (loghead 12 page-table-base-addr) 0))
  :enabled t
  :ignore-ok t

  (b* ((page-table-entry-addr
	(page-table-entry-addr lin-addr page-table-base-addr)))
      ;; 4K pages
      (list
       (addr-range 8 page-table-entry-addr))))

;; Page Directory:

(define ia32e-la-to-pa-page-directory-entry-validp
  ((lin-addr                 :type (signed-byte   #.*max-linear-address-size*))
   (page-directory-base-addr :type (unsigned-byte #.*physical-address-size*))
   (wp                       :type (unsigned-byte  1))
   (smep                     :type (unsigned-byte  1))
   (nxe                      :type (unsigned-byte  1))
   (r-w-x                    :type (member  :r :w :x))
   (cpl                      :type (unsigned-byte  2))
   (x86))
  :parents (reasoning-about-page-tables)
  :enabled t
  :guard (and (canonical-address-p lin-addr)
	      (equal (loghead 12 page-directory-base-addr) 0))
  :guard-hints (("Goal"
		 :in-theory (e/d (adding-7-to-shifted-bits)
				 (unsigned-byte-p
				  signed-byte-p
				  member-equal
				  not))))

  (let*
      ((page-directory-entry-addr
	(page-directory-entry-addr lin-addr page-directory-base-addr))
       (entry (rm-low-64 page-directory-entry-addr x86))
       (read-write (ia32e-page-tables-slice :r/w entry))
       (user-supervisor (ia32e-page-tables-slice :u/s entry))
       (execute-disable (ia32e-page-tables-slice :xd entry))
       (page-size (ia32e-page-tables-slice :ps  entry)))

    (and
     (equal (ia32e-page-tables-slice :p entry) 1)
     (not
      (or (and (equal page-size 1)
	       (not (equal (part-select entry :low 13 :high 20) 0)))
	  (not (equal (part-select entry
				   :low *physical-address-size*
				   :high 62)
		      0))
	  (and (equal nxe 0)
	       (not (equal (ia32e-page-tables-slice :xd entry) 0)))))
     (not
      (or
       ;; Read fault:
       (and (equal r-w-x :r)
	    (if (< cpl 3)
		nil
	      (equal user-supervisor 0)))
       ;; Write fault:
       (and (equal r-w-x :w)
	    (if (< cpl 3)
		(and (equal wp 1)
		     (equal read-write 0))
	      (or (equal user-supervisor 0)
		  (equal read-write 0))))
       ;; Instruction fetch fault:
       (and (equal r-w-x :x)
	    (if (< cpl 3)
		(and (equal nxe 1)
		     (equal execute-disable 1))
	      (or (equal user-supervisor 0)
		  (and (equal nxe 1)
		       (equal execute-disable 1)))))))

     (if (equal (ia32e-page-tables-slice :ps  entry) 0)
	 ;; 4K pages
	 (ia32e-la-to-pa-page-table-entry-validp
	  lin-addr
	  (ash (ia32e-pde-pg-table-slice :pde-pt entry) 12)
	  (ia32e-page-tables-slice :u/s entry)
	  wp smep nxe r-w-x cpl x86)
       t))))

(define translation-governing-addresses-for-page-directory
  ((lin-addr                 :type (signed-byte   #.*max-linear-address-size*))
   (page-directory-base-addr :type (unsigned-byte #.*physical-address-size*))
   (x86))
  :parents (reasoning-about-page-tables)
  :guard (and (canonical-address-p lin-addr)
	      (equal (loghead 12 page-directory-base-addr) 0))
  :guard-hints (("Goal" :in-theory (e/d* (canonical-address-p)
					 (translation-governing-addresses-for-page-table
					  ia32e-la-to-pa-page-table-entry-validp
					  unsigned-byte-p
					  signed-byte-p
					  acl2::commutativity-of-logior))))
  :enabled t

  (b* (
       ;; 2M pages:
       (page-directory-entry-addr
	(page-directory-entry-addr lin-addr page-directory-base-addr))
       (page-directory-entry (rm-low-64 page-directory-entry-addr x86))

       (pde-ps? (equal (ia32e-page-tables-slice :ps page-directory-entry) 1))
       ((when pde-ps?)
	(list (addr-range 8 page-directory-entry-addr)))

       ;; 4K pages:
       (page-table-base-addr
	(ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
       (page-table-addresses
	(translation-governing-addresses-for-page-table
	 lin-addr page-table-base-addr x86)))

      (append
       (list (addr-range 8 page-directory-entry-addr))
       page-table-addresses)))

;; Page Directory Pointer Table:

(define ia32e-la-to-pa-page-dir-ptr-table-entry-validp
  ((lin-addr            :type (signed-byte   #.*max-linear-address-size*))
   (ptr-table-base-addr :type (unsigned-byte #.*physical-address-size*))
   (wp                  :type (unsigned-byte  1))
   (smep                :type (unsigned-byte  1))
   (nxe                 :type (unsigned-byte  1))
   (r-w-x               :type (member  :r :w :x))
   (cpl                 :type (unsigned-byte  2))
   (x86))

  :parents (reasoning-about-page-tables)

  :enabled t
  :guard (and (canonical-address-p lin-addr)
	      (equal (loghead 12 ptr-table-base-addr) 0))
  :guard-hints (("Goal"
		 :in-theory (e/d (adding-7-to-shifted-bits)
				 (unsigned-byte-p
				  signed-byte-p
				  member-equal
				  not))))

  (let*
      ((ptr-table-entry-addr
	(page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
       (entry (rm-low-64 ptr-table-entry-addr x86))
       (read-write (ia32e-page-tables-slice :r/w entry))
       (user-supervisor (ia32e-page-tables-slice :u/s entry))
       (execute-disable (ia32e-page-tables-slice :xd entry))
       (page-size (ia32e-page-tables-slice :ps  entry)))

    (and
     (equal (ia32e-page-tables-slice :p entry) 1)
     (not (and (equal page-size 1)
	       (not (equal (part-select entry :low 13 :high 29) 0))))
     (not
      (or
       ;; Read fault:
       (and (equal r-w-x :r)
	    (if (< cpl 3)
		nil
	      (equal user-supervisor 0)))
       ;; Write fault:
       (and (equal r-w-x :w)
	    (if (< cpl 3)
		(and (equal wp 1)
		     (equal read-write 0))
	      (or (equal user-supervisor 0)
		  (equal read-write 0))))
       ;; Instructions fetch fault
       (and (equal r-w-x :x)
	    (if (< cpl 3)
		(and (equal nxe 1)
		     (equal execute-disable 1))
	      (or (equal user-supervisor 0)
		  (and (equal nxe 1)
		       (equal execute-disable 1)))))))

     (if (equal (ia32e-page-tables-slice :ps  entry) 0)
	 ;; 4K or 2M pages
	 (ia32e-la-to-pa-page-directory-entry-validp
	  lin-addr
	  (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd entry) 12)
	  wp smep nxe r-w-x cpl x86)
       t))))

(define translation-governing-addresses-for-page-dir-ptr-table
  ((lin-addr                 :type (signed-byte   #.*max-linear-address-size*))
   (ptr-table-base-addr :type (unsigned-byte #.*physical-address-size*))
   (x86))
  :parents (reasoning-about-page-tables)
  :guard (and (canonical-address-p lin-addr)
	      (equal (loghead 12 ptr-table-base-addr) 0))
  :guard-hints (("Goal" :in-theory (e/d* (canonical-address-p)
					 (translation-governing-addresses-for-page-directory
					  ia32e-la-to-pa-page-directory-entry-validp
					  unsigned-byte-p
					  signed-byte-p
					  acl2::commutativity-of-logior))))
  :enabled t

  (b* ((page-dir-ptr-table-entry-addr
	(page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
       (page-dir-ptr-table-entry (rm-low-64 page-dir-ptr-table-entry-addr x86))

       (pdpte-ps? (equal (ia32e-page-tables-slice :ps page-dir-ptr-table-entry) 1))

       ;; 1G pages:
       ((when pdpte-ps?)
	(list
	 (addr-range 8 page-dir-ptr-table-entry-addr)))

       ;; 2M or 4K pages:

       (page-directory-base-addr (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd page-dir-ptr-table-entry) 12))
       (page-directory-addresses
	(translation-governing-addresses-for-page-directory
	 lin-addr page-directory-base-addr x86)))

      (append (list (addr-range 8 page-dir-ptr-table-entry-addr))
	      page-directory-addresses)))


;; PML4 Table:

(define ia32e-la-to-pa-pml4-table-entry-validp
  ((lin-addr       :type (signed-byte   #.*max-linear-address-size*))
   (pml4-base-addr :type (unsigned-byte #.*physical-address-size*))
   (wp             :type (unsigned-byte  1))
   (smep           :type (unsigned-byte  1))
   (nxe            :type (unsigned-byte  1))
   (r-w-x          :type (member  :r :w :x))
   (cpl            :type (unsigned-byte  2))
   (x86))

  :parents (reasoning-about-page-tables)

  :enabled t
  :guard (and (canonical-address-p lin-addr)
	      (equal (loghead 12 pml4-base-addr) 0))
  :guard-hints (("Goal"
		 :in-theory (e/d (adding-7-to-shifted-bits)
				 (unsigned-byte-p
				  signed-byte-p
				  member-equal
				  not))))

  (let*
      ((pml4-entry-addr
	(pml4-table-entry-addr lin-addr pml4-base-addr))
       (entry (rm-low-64 pml4-entry-addr x86))
       (read-write (ia32e-page-tables-slice :r/w entry))
       (user-supervisor (ia32e-page-tables-slice :u/s entry))
       (execute-disable (ia32e-page-tables-slice :xd entry))
       (page-size (ia32e-page-tables-slice :ps  entry)))

    (and
     (equal (ia32e-page-tables-slice :p entry) 1)
     (not (or (not (equal page-size 0))
	      (and (equal nxe 0)
		   (not (equal execute-disable 0)))))
     (not
      (or
       ;; Read fault:
       (and (equal r-w-x :r)
	    (if (< cpl 3)
		nil
	      (equal user-supervisor 0)))
       ;; Write fault:
       (and (equal r-w-x :w)
	    (if (< cpl 3)
		(and (equal wp 1)
		     (equal read-write 0))
	      (or (equal user-supervisor 0)
		  (equal read-write 0))))
       ;; Instructions fetch fault:
       (and (equal r-w-x :x)
	    (if (< cpl 3)
		(and (equal nxe 1)
		     (equal execute-disable 1))
	      (or (equal user-supervisor 0)
		  (and (equal nxe 1)
		       (equal execute-disable 1)))))))

     (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
      lin-addr
      (ash (ia32e-pml4e-slice :pml4e-pdpt entry) 12)
      wp smep nxe r-w-x cpl x86))))

(define translation-governing-addresses-for-pml4-table
  ((lin-addr       :type (signed-byte   #.*max-linear-address-size*))
   (pml4-base-addr :type (unsigned-byte #.*physical-address-size*))
   (x86))

  :parents (reasoning-about-page-tables)
  :guard (and (canonical-address-p lin-addr)
	      (equal (loghead 12 pml4-base-addr) 0))
  :guard-hints (("Goal" :in-theory (e/d* (canonical-address-p)
					 (translation-governing-addresses-for-page-dir-ptr-table
					  ia32e-la-to-pa-page-dir-ptr-table-entry-validp
					  unsigned-byte-p
					  signed-byte-p
					  acl2::commutativity-of-logior))))
  :enabled t

  (b* ((pml4-entry-addr
	(pml4-table-entry-addr lin-addr pml4-base-addr))
       (pml4-entry (rm-low-64 pml4-entry-addr x86))

       ;; Page Directory Pointer Table:
       (ptr-table-base-addr
	(ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))

       (ptr-table-addresses
	(translation-governing-addresses-for-page-dir-ptr-table
	 lin-addr ptr-table-base-addr x86)))

      (append
       (list (addr-range 8 pml4-entry-addr))
       ptr-table-addresses)))

;; Top-level recognizer:

(define ia32e-la-to-pa-validp
  ((lin-addr  :type (signed-byte   #.*max-linear-address-size*))
   (r-w-x     :type (member  :r :w :x))
   (cpl       :type (unsigned-byte  2))
   (x86))

  :parents (reasoning-about-page-tables)

  :enabled t
  :guard (canonical-address-p lin-addr)
  :guard-hints (("Goal"
		 :in-theory (e/d ()
				 (unsigned-byte-p
				  signed-byte-p
				  member-equal
				  not))))
  (b* ((cr0 (n32 (ctri *cr0* x86)))
       (cr4 (n21 (ctri *cr4* x86)))
       (ia32-efer (n12 (msri *ia32_efer-idx* x86)))
       (wp (cr0-slice :cr0-wp cr0))
       (smep (cr4-slice :cr4-smep cr4))
       (nxe (ia32_efer-slice :ia32_efer-nxe ia32-efer))
       (cr3 (ctri *cr3* x86))
       (pml4-base-addr (ash (cr3-slice :cr3-pdb cr3) 12)))
      (ia32e-la-to-pa-pml4-table-entry-validp
       lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)))

(define translation-governing-addresses
  ((lin-addr :type (signed-byte   #.*max-linear-address-size*)
	     "Canonical linear address to be mapped to a physical address")
   (x86 "x86 state"))

  :parents (reasoning-about-page-tables)

  :long "<p>@('translation-governing-addresses') returns a
  @('true-listp') of physical addresses that govern the translation of
  a linear address @('lin-addr') to its corresponding physical address
  @('p-addr').  Addresses that can be a part of the
  output (depending on the page configurations, i.e., 4K, 2M, or 1G
  pages) include:</p>

<ol>
<li>The addresses of the relevant PML4 entry</li>

<li>The addresses of the relevant PDPT entry</li>

<li>The addresses of the relevant PD entry</li>

<li>The addresses of the relevant PT entry</li>

</ol>

<p>I intend to use this function for reasoning only, which is why I
don't have @('MBE')s to facilitate efficient execution.</p>"

  :guard-hints (("Goal" :in-theory (e/d* (canonical-address-p)
					 (translation-governing-addresses-for-pml4-table
					  ia32e-la-to-pa-pml4-table-entry-validp
					  unsigned-byte-p
					  signed-byte-p
					  acl2::commutativity-of-logior))))

  :enabled t

  (b* ((cr3       (ctri *cr3* x86))
       ;; PML4 Table:
       (pml4-base-addr (ash (cr3-slice :cr3-pdb cr3) 12)))

      (translation-governing-addresses-for-pml4-table
       lin-addr pml4-base-addr x86)))

(defthm consp-translation-governing-addresses
  (consp (translation-governing-addresses lin-addr x86))
  :rule-classes (:type-prescription :rewrite))

(defthm true-list-listp-translation-governing-addresses
  (true-list-listp (translation-governing-addresses lin-addr x86))
  :rule-classes (:type-prescription :rewrite))

;; ======================================================================

;; Rules that state when two paging entries are equal; this depends on
;; the appropriate parts of the linear address being equal.

(defthmd loghead-smaller-equality
  (implies (and (equal (loghead n x) (loghead n y))
		(natp n)
		(<= m n))
	   (equal (loghead m x) (loghead m y)))
  :hints
  (("Goal"
    :in-theory (e/d* (acl2::ihsext-recursive-redefs acl2::ihsext-inductions)
		     nil))))

(defruled equality-of-page-table-entry-addr
  :parents (reasoning-about-page-tables)
  (implies (equal (part-select lin-addr-1 :low 12 :high 20)
		  (part-select lin-addr-2 :low 12 :high 20))
	   (equal (page-table-entry-addr lin-addr-1 page-table-base-addr)
		  (page-table-entry-addr lin-addr-2 page-table-base-addr)))
  :use ((:instance loghead-smaller-equality
		   (x (logtail 12 lin-addr-1))
		   (y (logtail 12 lin-addr-2))
		   (n 40)
		   (m 9)))
  :in-theory (e/d (page-table-entry-addr)
		  (unsigned-byte-p
		   signed-byte-p)))

(defruled equality-of-page-directory-entry-addr
  :parents (reasoning-about-page-tables)
  (implies (equal (part-select lin-addr-1 :low 21 :high 29)
		  (part-select lin-addr-2 :low 21 :high 29))
	   (equal (page-directory-entry-addr lin-addr-1 page-directory-base-addr)
		  (page-directory-entry-addr lin-addr-2 page-directory-base-addr)))
  :use ((:instance loghead-smaller-equality
		   (x (logtail 12 lin-addr-1))
		   (y (logtail 12 lin-addr-2))
		   (n 40)
		   (m 9)))
  :in-theory (e/d (page-directory-entry-addr)
		  (unsigned-byte-p
		   signed-byte-p)))

(defruled equality-of-page-dir-ptr-table-entry-addr
  :parents (reasoning-about-page-tables)
  (implies (equal (part-select lin-addr-1 :low 30 :high 38)
		  (part-select lin-addr-2 :low 30 :high 38))
	   (equal (page-dir-ptr-table-entry-addr lin-addr-1 ptr-table-base-addr)
		  (page-dir-ptr-table-entry-addr lin-addr-2 ptr-table-base-addr)))
  :use ((:instance loghead-smaller-equality
		   (x (logtail 12 lin-addr-1))
		   (y (logtail 12 lin-addr-2))
		   (n 40)
		   (m 9)))
  :in-theory (e/d (page-dir-ptr-table-entry-addr)
		  (unsigned-byte-p
		   signed-byte-p)))

(defruled equality-of-pml4-table-entry-addr
  :parents (reasoning-about-page-tables)
  (implies (equal (part-select lin-addr-1 :low 39 :high 47)
		  (part-select lin-addr-2 :low 39 :high 47))
	   (equal (pml4-table-entry-addr lin-addr-1 pml4-table-base-addr)
		  (pml4-table-entry-addr lin-addr-2 pml4-table-base-addr)))
  :use ((:instance loghead-smaller-equality
		   (x (logtail 12 lin-addr-1))
		   (y (logtail 12 lin-addr-2))
		   (n 40)
		   (m 9)))
  :in-theory (e/d (pml4-table-entry-addr)
		  (unsigned-byte-p
		   signed-byte-p)))

;; ======================================================================

;; ia32e-la-to-pa-page-table:

(defmacro ia32e-la-to-pa-page-table-entry-components-equal-p-body
  (page-table-entry-1 page-table-entry-2)
  `(and (equal (ia32e-pte-4k-page-slice :pte-p   ,page-table-entry-1)
	       (ia32e-pte-4k-page-slice :pte-p   ,page-table-entry-2))
	(equal (ia32e-pte-4k-page-slice :pte-r/w ,page-table-entry-1)
	       (ia32e-pte-4k-page-slice :pte-r/w ,page-table-entry-2))
	(equal (ia32e-pte-4k-page-slice :pte-u/s ,page-table-entry-1)
	       (ia32e-pte-4k-page-slice :pte-u/s ,page-table-entry-2))
	(equal (ia32e-pte-4k-page-slice :pte-xd  ,page-table-entry-1)
	       (ia32e-pte-4k-page-slice :pte-xd  ,page-table-entry-2))
	;; Reserved bits are zero.
	;; (equal (loghead 11 (logtail 52 ,page-table-entry-2)) 0)
	(equal (loghead 11 (logtail 52 ,page-table-entry-1))
	       (loghead 11 (logtail 52 ,page-table-entry-2)))))

(define ia32e-la-to-pa-page-table-entry-components-equal-p
  (page-table-entry-1 page-table-entry-2)
  :verify-guards nil
  :non-executable t
  (ia32e-la-to-pa-page-table-entry-components-equal-p-body page-table-entry-1 page-table-entry-2))

(defmacro ia32e-la-to-pa-page-table-entry-components-equal-p-macro (x y)
  `(ia32e-la-to-pa-page-table-entry-components-equal-p-body ,x ,y))

(defthm ia32e-la-to-pa-page-table-entry-components-equal-p-reflexive
  (ia32e-la-to-pa-page-table-entry-components-equal-p b b)
  :hints (("Goal" :in-theory (e/d
			      (ia32e-la-to-pa-page-table-entry-components-equal-p)
			      ()))))

(defthm ia32e-la-to-pa-page-table-entry-components-equal-p-accessed-bit-set
  (ia32e-la-to-pa-page-table-entry-components-equal-p
   b (logior 32 (logand 18446744073709551583 b)))
  :hints (("Goal" :in-theory (e/d
			      (ia32e-la-to-pa-page-table-entry-components-equal-p)
			      ()))))

(defthm ia32e-la-to-pa-page-table-entry-components-equal-p-dirty-bit-set
  (ia32e-la-to-pa-page-table-entry-components-equal-p
   b (logior 64 (logand 18446744073709551551 b)))
  :hints (("Goal" :in-theory (e/d
			      (ia32e-la-to-pa-page-table-entry-components-equal-p)
			      ()))))

(defthm ia32e-la-to-pa-page-table-entry-components-equal-p-accessed-and-dirty-bits-set
  (ia32e-la-to-pa-page-table-entry-components-equal-p
   b (logior
      64
      (logand
       18446744073709551551
       (logior 32 (logand 18446744073709551583 b)))))
  :hints (("Goal" :in-theory (e/d
			      (ia32e-la-to-pa-page-table-entry-components-equal-p)
			      ()))))
;; ......................................................................
;; Rules about the three return values of ia32e-la-to-pa-page-table-entry:
;; ......................................................................

(defrule mv-nth-0-no-error-ia32e-la-to-pa-page-table
  :parents (reasoning-about-page-tables)
  (implies (ia32e-la-to-pa-page-table-entry-validp
	    lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
	   (equal (mv-nth
		   0
		   (ia32e-la-to-pa-page-table
		    lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86))
		  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-table)
		  ()))

(defrule mv-nth-0-no-error-ia32e-la-to-pa-page-table-with-disjoint-!memi
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
		 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))
		(disjoint-p (addr-range 1 addr)
			    (addr-range 8 page-table-entry-addr)))
	   (equal (mv-nth
		   0
		   (ia32e-la-to-pa-page-table
		    lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl
		    (xw :mem addr val x86)))
		  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-table)
		  (addr-range-1 not)))

(defrule mv-nth-0-no-error-ia32e-la-to-pa-page-table-with-disjoint-wm-low-64
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
		 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))
		(disjoint-p (addr-range 8 addr)
			    (addr-range 8 page-table-entry-addr))
		(integerp addr))
	   (equal (mv-nth
		   0
		   (ia32e-la-to-pa-page-table
		    lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl
		    (wm-low-64 addr val x86)))
		  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-table)
		  ()))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-page-table
  :parents (reasoning-about-page-tables)
  (implies (ia32e-la-to-pa-page-table-entry-validp
	    lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
	   (equal (mv-nth
		   1
		   (ia32e-la-to-pa-page-table
		    lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86))
		  (part-install
		   (part-select lin-addr :low 0 :high 11)
		   (ash (ia32e-pte-4K-page-slice
			 :pte-page
			 (rm-low-64 (page-table-entry-addr lin-addr page-table-base-addr)
				    x86))
			12)
		   :low 0 :high 11)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-table)
		  ()))

(defruled mv-nth-1-no-error-ia32e-la-to-pa-page-table-different-components
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
		 lin-addr page-table-base-addr u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-page-table-entry-validp
		 lin-addr page-table-base-addr u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))
	   (equal (mv-nth
		   1
		   (ia32e-la-to-pa-page-table
		    lin-addr page-table-base-addr u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86))
		  (mv-nth
		   1
		   (ia32e-la-to-pa-page-table
		    lin-addr page-table-base-addr u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
  :do-not '(preprocess)
  :in-theory (e/d () (ia32e-la-to-pa-page-table-entry-validp)))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-page-table-with-disjoint-!memi
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
		 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))
		(disjoint-p (addr-range 1 addr)
			    (addr-range 8 page-table-entry-addr)))
	   (equal (mv-nth
		   1
		   (ia32e-la-to-pa-page-table
		    lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl
		    (xw :mem addr val x86)))
		  (mv-nth
		   1
		   (ia32e-la-to-pa-page-table
		    lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl
		    x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-table)
		  (addr-range-1 not)))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-page-table-with-disjoint-wm-low-64
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
		 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))
		(disjoint-p (addr-range 8 addr)
			    (addr-range 8 page-table-entry-addr))
		(integerp addr))
	   (equal (mv-nth
		   1
		   (ia32e-la-to-pa-page-table
		    lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl
		    (wm-low-64 addr val x86)))
		  (mv-nth
		   1
		   (ia32e-la-to-pa-page-table
		    lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl
		    x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-table)
		  ()))

(defrule mv-nth-2-no-error-ia32e-la-to-pa-page-table
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
		 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)

		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))
		(equal page-table-entry (rm-low-64 page-table-entry-addr x86))

		(equal accessed (ia32e-page-tables-slice :a page-table-entry))
		(equal dirty (ia32e-page-tables-slice :d page-table-entry))

		(equal accessed-entry
		       (if (equal accessed 0)
			   (!ia32e-page-tables-slice :a 1 page-table-entry)
			 page-table-entry))
		(equal dirty-entry
		       (if (and (equal dirty 0)
				(equal r-w-x :w))
			   (!ia32e-page-tables-slice :d 1 accessed-entry)
			 accessed-entry))
		(equal dirty-x86
		       (if (or (equal accessed 0)
			       (and (equal dirty 0)
				    (equal r-w-x :w)))
			   (wm-low-64 page-table-entry-addr dirty-entry x86)
			 x86)))
	   (equal (mv-nth
		   2
		   (ia32e-la-to-pa-page-table
		    lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86))
		  dirty-x86))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-table)
		  (not)))

;; ......................................................................
;; Reading page-table-entry-addr again using rm-low-64:
;; ......................................................................

(defruled rm-low-64-and-page-table
  :parents (reasoning-about-page-tables)
  ;; Note that the conclusion of this theorem is very similar to
  ;; theorems about other page-table-entry accessor functions.  After all, all
  ;; paging data structures are modified in the same way.
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
		 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))
		(equal page-table-entry (rm-low-64 page-table-entry-addr x86))
		(physical-address-p page-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 page-table-base-addr) 0)
		(x86p x86))
	   (equal (rm-low-64 page-table-entry-addr
			     (mv-nth
			      2
			      (ia32e-la-to-pa-page-table
			       lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)))
		  (cond
		   ( ;; Accessed and dirty bits are set.
		    (and (equal (ia32e-page-tables-slice :a page-table-entry) 1)
			 (equal (ia32e-page-tables-slice :d page-table-entry) 1))
		    (rm-low-64 page-table-entry-addr x86))

		   ( ;; Accessed bit is set and dirty bit is clear and
		    ;; memory write is being done.
		    (and (equal (ia32e-page-tables-slice :a page-table-entry) 1)
			 (equal (ia32e-page-tables-slice :d page-table-entry) 0)
			 (equal r-w-x :w))
		    (!ia32e-page-tables-slice :d 1 (rm-low-64 page-table-entry-addr x86)))

		   ( ;; Accessed bit is set and dirty bit is clear and
		    ;; memory write is not being done.
		    (and (equal (ia32e-page-tables-slice :a page-table-entry) 1)
			 (equal (ia32e-page-tables-slice :d page-table-entry) 0)
			 (not (equal r-w-x :w)))
		    (rm-low-64 page-table-entry-addr x86))

		   ( ;; Accessed and dirty bits are clear and memory
		    ;; write is being done.
		    (and (equal (ia32e-page-tables-slice :a page-table-entry) 0)
			 (equal (ia32e-page-tables-slice :d page-table-entry) 0)
			 (equal r-w-x :w))
		    (!ia32e-page-tables-slice
		     :d 1
		     (!ia32e-page-tables-slice
		      :a 1
		      (rm-low-64 page-table-entry-addr x86))))

		   ( ;; Accessed bit and dirty bits are clear and memory
		    ;; write is not being done.
		    (and (equal (ia32e-page-tables-slice :a page-table-entry) 0)
			 (equal (ia32e-page-tables-slice :d page-table-entry) 0)
			 (not (equal r-w-x :w)))
		    (!ia32e-page-tables-slice :a 1 (rm-low-64 page-table-entry-addr x86)))

		   (t
		    ;; This shouldn't be reached.
		    (rm-low-64 page-table-entry-addr
			       (mv-nth
				2
				(ia32e-la-to-pa-page-table
				 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)))))))

  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-table)
		  (not
		   unsigned-byte-p
		   signed-byte-p)))

;; ......................................................................
;; !memi and state after data structure walk WoW theorem:
;; ......................................................................

(defrule disjoint-!memi-mv-nth-2-no-error-ia32e-la-to-pa-page-table
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
		 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))
		(disjoint-p (addr-range 1 addr)
			    (addr-range 8 page-table-entry-addr))
		(integerp addr))
	   (equal
	    (mv-nth 2 (ia32e-la-to-pa-page-table
		       lin-addr page-table-base-addr u-s-acc wp smep
		       nxe r-w-x cpl
		       (xw :mem addr val x86)))
	    (xw :mem addr val
		   (mv-nth 2 (ia32e-la-to-pa-page-table
			      lin-addr page-table-base-addr u-s-acc wp smep
			      nxe r-w-x cpl x86)))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-table)
		  (not
		   addr-range-1)))

;; ......................................................................
;; Reading addresses disjoint from page-table-entry-addr after walking
;; the page table:
;; ......................................................................

(defrule disjoint-memi-mv-nth-2-no-error-ia32e-la-to-pa-page-table
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
		 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))
		(disjoint-p (addr-range 1 addr)
			    (addr-range 8 page-table-entry-addr)))
	   (equal
	    (xr :mem
	     addr
	     (mv-nth 2 (ia32e-la-to-pa-page-table
			lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)))
	    (xr :mem addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-table)
		  (not
		   addr-range-1)))

(defrule disjoint-rm-low-64-mv-nth-2-no-error-ia32e-la-to-pa-page-table
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
		 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))
		(disjoint-p (addr-range 8 addr)
			    (addr-range 8 page-table-entry-addr))
		(integerp addr))
	   (equal
	    (rm-low-64
	     addr
	     (mv-nth 2 (ia32e-la-to-pa-page-table
			lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)))
	    (rm-low-64 addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-table)
		  (not)))

(defrule disjoint-rm-low-32-mv-nth-2-no-error-ia32e-la-to-pa-page-table
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
		 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))
		(disjoint-p (addr-range 4 addr)
			    (addr-range 8 page-table-entry-addr))
		(integerp addr))
	   (equal
	    (rm-low-32
	     addr
	     (mv-nth 2 (ia32e-la-to-pa-page-table
			lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)))
	    (rm-low-32 addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-table
		   wm-low-64)
		  (not)))

;; ......................................................................
;; Theorems that state that the validity of the page table entry is
;; preserved when writes are done to disjoint addresses or :a/:d are
;; set:
;; ......................................................................

(defrule page-table-entry-with-disjoint-!memi-still-valid-ia32e-la-to-pa-page-table
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
		 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))
		(disjoint-p
		 (addr-range 1 addr)
		 (addr-range 8 page-table-entry-addr)))
	   (ia32e-la-to-pa-page-table-entry-validp
	    lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl
	    (xw :mem addr val x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-table)
		  (not addr-range-1
		       unsigned-byte-p
		       signed-byte-p)))

(defrule page-table-entry-with-disjoint-wm-low-64-still-valid-ia32e-la-to-pa-page-table
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
		 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))
		(disjoint-p
		 (addr-range 8 addr)
		 (addr-range 8 page-table-entry-addr))
		(integerp addr))
	   (ia32e-la-to-pa-page-table-entry-validp
	    lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl
	    (wm-low-64 addr val x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-table)
		  (not
		   unsigned-byte-p
		   signed-byte-p)))

(defrule page-table-entry-with-accessed-bit-set-still-valid-ia32e-la-to-pa-page-table
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
		 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))
		(equal page-table-entry (rm-low-64 page-table-entry-addr x86))

		(physical-address-p page-table-base-addr)
		(canonical-address-p lin-addr)
		(x86p x86))

	   (ia32e-la-to-pa-page-table-entry-validp
	    lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl
	    (wm-low-64
	     page-table-entry-addr
	     ;; (!ia32e-page-tables-slice :a 1 page-table-entry)
	     (logior 32 (logand 18446744073709551583 page-table-entry))
	     x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-table)
		  (not
		   unsigned-byte-p
		   signed-byte-p)))

(defrule page-table-entry-with-dirty-bit-set-still-valid-ia32e-la-to-pa-page-table
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
		 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))
		(equal page-table-entry (rm-low-64 page-table-entry-addr x86))

		(physical-address-p page-table-base-addr)
		(canonical-address-p lin-addr)
		(x86p x86))

	   (ia32e-la-to-pa-page-table-entry-validp
	    lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl
	    (wm-low-64
	     page-table-entry-addr
	     ;; (!ia32e-page-tables-slice :d 1 page-table-entry)
	     (logior 64 (logand 18446744073709551551 page-table-entry))
	     x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-table)
		  (not
		   unsigned-byte-p
		   signed-byte-p)))

(defrule page-table-entry-with-accessed-and-dirty-bits-set-still-valid-ia32e-la-to-pa-page-table
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
		 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))
		(equal page-table-entry (rm-low-64 page-table-entry-addr x86))

		(physical-address-p page-table-base-addr)
		(canonical-address-p lin-addr)
		(x86p x86))

	   (ia32e-la-to-pa-page-table-entry-validp
	    lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl
	    (wm-low-64
	     page-table-entry-addr
	     ;; (!ia32e-page-tables-slice :d 1 (!ia32e-page-tables-slice :a 1 page-table-entry))
	     (logior
	      64
	      (logand
	       18446744073709551551
	       (logior 32 (logand 18446744073709551583 page-table-entry))))
	     x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-table)
		  (not
		   unsigned-byte-p
		   signed-byte-p)))

;; ......................................................................
;; Reading page table entry from x86 states where :a/:d are set:
;; ......................................................................

(defrule reading-entry-with-accessed-bit-set-ia32e-la-to-pa-page-table
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
		 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))
		(equal page-table-entry (rm-low-64 page-table-entry-addr x86))
		(physical-address-p page-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 page-table-base-addr) 0)
		(x86p x86))

	   (equal
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-table
	      lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl
	      (wm-low-64
	       page-table-entry-addr
	       ;; (!ia32e-page-tables-slice :a 1 page-table-entry)
	       (logior 32 (logand 18446744073709551583 page-table-entry))
	       x86)))
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-table
	      lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d ()
		  (not
		   mv-nth-2-no-error-ia32e-la-to-pa-page-table
		   unsigned-byte-p
		   signed-byte-p)))

(defrule reading-entry-with-dirty-bit-set-ia32e-la-to-pa-page-table
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
		 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))
		(equal page-table-entry (rm-low-64 page-table-entry-addr x86))
		(physical-address-p page-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 page-table-base-addr) 0)
		(x86p x86))

	   (equal
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-table
	      lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl
	      (wm-low-64
	       page-table-entry-addr
	       ;; (!ia32e-page-tables-slice :d 1 page-table-entry)
	       (logior 64 (logand 18446744073709551551 page-table-entry))
	       x86)))
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-table
	      lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d ()
		  (not
		   mv-nth-2-no-error-ia32e-la-to-pa-page-table
		   unsigned-byte-p
		   signed-byte-p)))

(defrule reading-entry-with-accessed-and-dirty-bits-set-ia32e-la-to-pa-page-table
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
		 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))
		(equal page-table-entry (rm-low-64 page-table-entry-addr x86))
		(physical-address-p page-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 page-table-base-addr) 0)
		(x86p x86))

	   (equal
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-table
	      lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl
	      (wm-low-64
	       page-table-entry-addr
	       ;; (!ia32e-page-tables-slice :d 1 (!ia32e-page-tables-slice :a 1 page-table-entry))
	       (logior
		64
		(logand
		 18446744073709551551
		 (logior 32 (logand 18446744073709551583 page-table-entry))))
	       x86)))
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-table
	      lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d ()
		  (not
		   mv-nth-2-no-error-ia32e-la-to-pa-page-table
		   unsigned-byte-p
		   signed-byte-p)))

;; ......................................................................
;; More theorems about preservation of validity of page table entries:
;; ......................................................................

(defrule relating-validity-of-two-entries-in-two-x86-states-wrt-page-table-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
		 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))
		(equal page-table-entry-1 (rm-low-64 page-table-entry-addr x86))
		(equal page-table-entry-2 (rm-low-64 page-table-entry-addr x86-another))
		(ia32e-la-to-pa-page-table-entry-components-equal-p
		 page-table-entry-1 page-table-entry-2))

	   (ia32e-la-to-pa-page-table-entry-validp
	    lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl
	    x86-another))
  :in-theory (e/d (ia32e-la-to-pa-page-table-entry-components-equal-p)
		  ()))

(defruled page-table-components-equal-rm-low-64-of-table-page-table-entry-addr-via-page-table-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
		 lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))
		(equal page-table-entry (rm-low-64 page-table-entry-addr x86))
		(physical-address-p page-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 page-table-base-addr) 0)
		(x86p x86))

	   (ia32e-la-to-pa-page-table-entry-components-equal-p
	    (rm-low-64 page-table-entry-addr x86)
	    (rm-low-64
	     page-table-entry-addr
	     (mv-nth
	      2
	      (ia32e-la-to-pa-page-table
	       lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)))))
  :hints (("Goal" :do-not '(preprocess)
	   :in-theory (e/d (rm-low-64-and-page-table
			    ia32e-la-to-pa-page-table-entry-components-equal-p)
			   (not
			    member-p-cons
			    disjoint-p-cons
			    ia32e-la-to-pa-page-table-entry-validp
			    unsigned-byte-p
			    signed-byte-p)))))

(defrule re-read-entry-still-valid-ia32e-la-to-pa-page-table
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
		 lin-addr page-table-base-addr u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-page-table-entry-validp
		 lin-addr page-table-base-addr u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
		(physical-address-p page-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 page-table-base-addr) 0)
		(x86p x86))
	   (ia32e-la-to-pa-page-table-entry-validp
	    lin-addr page-table-base-addr u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
	    (mv-nth
	     2
	     (ia32e-la-to-pa-page-table
	      lin-addr page-table-base-addr u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
  :do-not '(preprocess)
  :in-theory (e/d (page-table-components-equal-rm-low-64-of-table-page-table-entry-addr-via-page-table-4K-pages)
		  (ia32e-la-to-pa-page-table-entry-validp
		   mv-nth-2-no-error-ia32e-la-to-pa-page-table
		   not
		   unsigned-byte-p
		   signed-byte-p)))

;; ......................................................................
;; Two page table walks --- same paging entry:
;; ......................................................................

(defrule two-page-table-walks-ia32e-la-to-pa-page-table-same-addresses
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
		 lin-addr page-table-base-addr u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-page-table-entry-validp
		 lin-addr page-table-base-addr u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
		(physical-address-p page-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 page-table-base-addr) 0)
		(x86p x86))
	   (equal
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-table
	      lin-addr page-table-base-addr u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
	      (mv-nth
	       2
	       (ia32e-la-to-pa-page-table
		lin-addr page-table-base-addr u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-table
	      lin-addr page-table-base-addr u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1
	      cpl-1 x86))))
  :in-theory (e/d ()
		  (ia32e-la-to-pa-page-table-entry-validp
		   mv-nth-1-no-error-ia32e-la-to-pa-page-table))
  :do-not '(preprocess))

(defrule two-page-table-walks-ia32e-la-to-pa-page-table-same-entry-different-addrs
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
		 lin-addr-1 page-table-base-addr u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-page-table-entry-validp
		 lin-addr-2 page-table-base-addr u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)

		(equal (part-select lin-addr-1 :low 12 :high 20)
		       (part-select lin-addr-2 :low 12 :high 20))
		(not (equal (part-select lin-addr-1 :low 0 :width 12)
			    (part-select lin-addr-2 :low 0 :width 12)))

		(physical-address-p page-table-base-addr)
		(canonical-address-p lin-addr-1)
		(canonical-address-p lin-addr-2)
		(equal (loghead 12 page-table-base-addr) 0)
		(x86p x86))
	   (equal
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-table
	      lin-addr-1 page-table-base-addr u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
	      (mv-nth
	       2
	       (ia32e-la-to-pa-page-table
		lin-addr-2 page-table-base-addr u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-table
	      lin-addr-1 page-table-base-addr u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1
	      cpl-1 x86))))
  :use ((:instance equality-of-page-table-entry-addr))
  :in-theory (e/d ()
		  (ia32e-la-to-pa-page-table-entry-validp
		   mv-nth-1-no-error-ia32e-la-to-pa-page-table
		   unsigned-byte-p
		   signed-byte-p))
  :do-not '(preprocess))

;; ......................................................................
;; Two page table walks --- different paging entries:
;; ......................................................................

(defrule two-page-table-walks-ia32e-la-to-pa-page-table-different-entries
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
		 lin-addr-1 page-table-base-addr-1 u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-page-table-entry-validp
		 lin-addr-2 page-table-base-addr-2 u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)

		(equal page-table-entry-addr-1
		       (page-table-entry-addr lin-addr-1 page-table-base-addr-1))
		(equal page-table-entry-addr-2
		       (page-table-entry-addr lin-addr-2 page-table-base-addr-2))

		(disjoint-p
		 (addr-range 8 page-table-entry-addr-2)
		 (addr-range 8 page-table-entry-addr-1))

		(physical-address-p page-table-base-addr-1)
		(physical-address-p page-table-base-addr-2)
		(x86p x86))
	   (equal
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-table
	      lin-addr-1 page-table-base-addr-1 u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
	      (mv-nth
	       2
	       (ia32e-la-to-pa-page-table
		lin-addr-2 page-table-base-addr-2 u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-table
	      lin-addr-1 page-table-base-addr-1 u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1
	      cpl-1 x86))))
  :in-theory (e/d ()
		  (ia32e-la-to-pa-page-table-entry-validp
		   mv-nth-1-no-error-ia32e-la-to-pa-page-table
		   unsigned-byte-p
		   signed-byte-p
		   member-p-cons
		   disjoint-p-cons))
  :do-not '(preprocess))

;; ......................................................................
;; More theorems about validity of page table entries being
;; preserved when the translation-governing addresses are disjoint:
;; ......................................................................

(defrule validity-preserved-same-x86-state-disjoint-addresses-wrt-page-table
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-table-entry-validp
		 lin-addr-1 page-table-base-addr-1 u-s-acc-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-page-table-entry-validp
		 lin-addr-2 page-table-base-addr-2 u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)

		(pairwise-disjoint-p
		 (append
		  (translation-governing-addresses-for-page-table
		   lin-addr-1 page-table-base-addr-1 x86)
		  (translation-governing-addresses-for-page-table
		   lin-addr-2 page-table-base-addr-2 x86)))

		(physical-address-p page-table-base-addr-1)
		(physical-address-p page-table-base-addr-2)
		(x86p x86))
	   (ia32e-la-to-pa-page-table-entry-validp
	    lin-addr-1 page-table-base-addr-1 u-s-acc-1 wp-1 smep-1
	    nxe-1 r-w-x-1 cpl-1
	    (mv-nth 2
		    (ia32e-la-to-pa-page-table
		     lin-addr-2 page-table-base-addr-2 u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
  :in-theory (e/d
	      ()
	      (ia32e-la-to-pa-page-table-entry-validp
	       addr-range-1
	       mv-nth-2-no-error-ia32e-la-to-pa-page-table
	       member-p-cons
	       disjoint-p-cons
	       not
	       unsigned-byte-p
	       signed-byte-p)))

;; ......................................................................
;; Translation-Governing-Addresses-For-Page-Table and
;; ia32e-la-to-pa-page-table-entry:
;; ......................................................................

(defrule translation-governing-addresses-for-page-table-and-ia32e-la-to-pa-page-table
  :parents (reasoning-about-page-tables)
  (equal
   (translation-governing-addresses-for-page-table
    lin-addr-1 page-table-base-addr-1
    (mv-nth 2
	    (ia32e-la-to-pa-page-table
	     lin-addr-2 page-table-base-addr-2 u-s-acc-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)))
   (translation-governing-addresses-for-page-table
    lin-addr-1 page-table-base-addr-1 x86))
  :in-theory (e/d ()
		  (ia32e-la-to-pa-page-table-entry-validp
		   addr-range-1
		   mv-nth-2-no-error-ia32e-la-to-pa-page-table
		   member-p-cons
		   disjoint-p-cons
		   not
		   unsigned-byte-p
		   signed-byte-p)))

(in-theory (e/d () (ia32e-la-to-pa-page-table-entry-validp)))

;; ======================================================================

;; ia32e-la-to-pa-page-directory:

(defmacro ia32e-la-to-pa-page-directory-entry-components-equal-p-2M-body
  (page-directory-entry-1 page-directory-entry-2)
  `(and (equal (ia32e-pde-2MB-page-slice :pde-p    ,page-directory-entry-1)
	       (ia32e-pde-2MB-page-slice :pde-p    ,page-directory-entry-2))
	(equal (ia32e-pde-2MB-page-slice :pde-r/w  ,page-directory-entry-1)
	       (ia32e-pde-2MB-page-slice :pde-r/w  ,page-directory-entry-2))
	(equal (ia32e-pde-2MB-page-slice :pde-u/s  ,page-directory-entry-1)
	       (ia32e-pde-2MB-page-slice :pde-u/s  ,page-directory-entry-2))
	(equal (ia32e-pde-2MB-page-slice :pde-ps   ,page-directory-entry-1)
	       (ia32e-pde-2MB-page-slice :pde-ps   ,page-directory-entry-2))
	(equal (ia32e-pde-2MB-page-slice :pde-xd   ,page-directory-entry-1)
	       (ia32e-pde-2MB-page-slice :pde-xd   ,page-directory-entry-2))
	;; Reserved bits are zero.
	;; (equal (loghead 11 (logtail 52 ,page-directory-entry-2)) 0)
	;; (equal (loghead  8 (logtail 13 ,page-directory-entry-2)) 0)
	(equal (loghead 11 (logtail 52 ,page-directory-entry-1))
	       (loghead 11 (logtail 52 ,page-directory-entry-2)))
	(equal (loghead  8 (logtail 13 ,page-directory-entry-1))
	       (loghead  8 (logtail 13 ,page-directory-entry-2)))))

(defmacro ia32e-la-to-pa-page-directory-entry-components-equal-p-4K-body
  (page-directory-entry-1 page-directory-entry-2)
  `(and (equal (ia32e-pde-pg-table-slice :pde-p     ,page-directory-entry-1)
	       (ia32e-pde-pg-table-slice :pde-p     ,page-directory-entry-2))
	(equal (ia32e-pde-pg-table-slice :pde-r/w   ,page-directory-entry-1)
	       (ia32e-pde-pg-table-slice :pde-r/w   ,page-directory-entry-2))
	(equal (ia32e-pde-pg-table-slice :pde-u/s   ,page-directory-entry-1)
	       (ia32e-pde-pg-table-slice :pde-u/s   ,page-directory-entry-2))
	(equal (ia32e-pde-pg-table-slice :pde-ps    ,page-directory-entry-1)
	       (ia32e-pde-pg-table-slice :pde-ps    ,page-directory-entry-2))
	(equal (ia32e-pde-pg-table-slice :pde-pt    ,page-directory-entry-1)
	       (ia32e-pde-pg-table-slice :pde-pt    ,page-directory-entry-2))
	(equal (ia32e-pde-pg-table-slice :pde-xd    ,page-directory-entry-1)
	       (ia32e-pde-pg-table-slice :pde-xd    ,page-directory-entry-2))
	;; Reserved bits are zero.
	;; (equal (loghead 11 (logtail 52 ,page-directory-entry-2)) 0)
	(equal (loghead 11 (logtail 52 ,page-directory-entry-1))
	       (loghead 11 (logtail 52 ,page-directory-entry-2)))))

(define ia32e-la-to-pa-page-directory-entry-components-equal-p
  (page-size? page-directory-entry-1 page-directory-entry-2)
  :verify-guards nil
  :non-executable t
  (if (equal page-size? '2M)
      (ia32e-la-to-pa-page-directory-entry-components-equal-p-2M-body
       page-directory-entry-1 page-directory-entry-2)
    (if (equal page-size? '4K)
	(ia32e-la-to-pa-page-directory-entry-components-equal-p-4K-body
	 page-directory-entry-1 page-directory-entry-2)
      't)))

(defmacro ia32e-la-to-pa-page-directory-entry-components-equal-p-4K-macro (x y)
  `(ia32e-la-to-pa-page-directory-entry-components-equal-p-4K-body ,x ,y))

(defmacro ia32e-la-to-pa-page-directory-entry-components-equal-p-2M-macro (x y)
  `(ia32e-la-to-pa-page-directory-entry-components-equal-p-2M-body ,x
  ,y))

(defthm ia32e-la-to-pa-page-directory-entry-components-equal-p-reflexive
  (ia32e-la-to-pa-page-directory-entry-components-equal-p a b b)
  :hints (("Goal" :in-theory (e/d
			      (ia32e-la-to-pa-page-directory-entry-components-equal-p)
			      ()))))

(defthm ia32e-la-to-pa-page-directory-entry-components-equal-p-accessed-bit-set
  (ia32e-la-to-pa-page-directory-entry-components-equal-p
   a b (logior 32 (logand 18446744073709551583 b)))
  :hints (("Goal" :in-theory (e/d
			      (ia32e-la-to-pa-page-directory-entry-components-equal-p)
			      ()))))

(defthm ia32e-la-to-pa-page-directory-entry-components-equal-p-dirty-bit-set
  (ia32e-la-to-pa-page-directory-entry-components-equal-p
   a b (logior 64 (logand 18446744073709551551 b)))
  :hints (("Goal" :in-theory (e/d
			      (ia32e-la-to-pa-page-directory-entry-components-equal-p)
			      ()))))

(defthm ia32e-la-to-pa-page-directory-entry-components-equal-p-accessed-and-dirty-bits-set
  (ia32e-la-to-pa-page-directory-entry-components-equal-p
   a b (logior
	64
	(logand
	 18446744073709551551
	 (logior 32 (logand 18446744073709551583 b)))))
  :hints (("Goal" :in-theory (e/d
			      (ia32e-la-to-pa-page-directory-entry-components-equal-p)
			      ()))))

;; ......................................................................
;; Establishing inferior data structure entry validity from page
;; directory entry's validity:
;; ......................................................................

(defrule page-directory-entry-validp-to-page-table-entry-validp
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry)
			    12))
		(equal u-s-acc
		       (ia32e-page-tables-slice :u/s page-directory-entry)))
	   (ia32e-la-to-pa-page-table-entry-validp
	    lin-addr page-table-base-addr u-s-acc
	    wp smep nxe r-w-x cpl x86))
  :rule-classes (:rewrite :forward-chaining))

;; ......................................................................
;; Rules about the three return values of ia32e-la-to-pa-page-directory-entry:
;; ......................................................................

(defrule mv-nth-0-no-error-ia32e-la-to-pa-page-directory
  :parents (reasoning-about-page-tables)
  (implies (ia32e-la-to-pa-page-directory-entry-validp
	    lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
	   (equal (mv-nth
		   0
		   (ia32e-la-to-pa-page-directory
		    lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86))
		  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory)
		  (not)))

;; 2M pages:

(defrule mv-nth-0-no-error-ia32e-la-to-pa-page-directory-2M-pages-with-disjoint-!memi
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  page-directory-entry) 1)
		(disjoint-p
		 (addr-range 1 addr)
		 (addr-range 8 page-directory-entry-addr)))
	   (equal (mv-nth
		   0
		   (ia32e-la-to-pa-page-directory
		    lin-addr page-directory-base-addr wp smep nxe r-w-x cpl
		    (xw :mem addr val x86)))
		  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory)
		  (not addr-range-1)))

(defrule mv-nth-0-no-error-ia32e-la-to-pa-page-directory-2M-pages-with-disjoint-wm-low-64
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  page-directory-entry) 1)
		(disjoint-p
		 (addr-range 8 addr)
		 (addr-range 8 page-directory-entry-addr))
		(integerp addr))
	   (equal (mv-nth
		   0
		   (ia32e-la-to-pa-page-directory
		    lin-addr page-directory-base-addr wp smep nxe r-w-x cpl
		    (wm-low-64 addr val x86)))
		  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory)
		  (not)))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-page-directory-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  page-directory-entry) 1))

	   (equal (mv-nth
		   1
		   (ia32e-la-to-pa-page-directory
		    lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86))
		  (part-install
		   (part-select lin-addr :low 0 :high 20)
		   (ash (ia32e-pde-2MB-page-slice :pde-page page-directory-entry) 21)
		   :low 0 :high 20)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory)
		  (not)))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-page-directory-2M-pages-with-disjoint-!memi
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  page-directory-entry) 1)
		(disjoint-p
		 (addr-range 1 addr)
		 (addr-range 8 page-directory-entry-addr))
		(integerp addr))

	   (equal (mv-nth
		   1
		   (ia32e-la-to-pa-page-directory
		    lin-addr page-directory-base-addr wp smep nxe r-w-x cpl
		    (xw :mem addr val x86)))
		  (mv-nth
		   1
		   (ia32e-la-to-pa-page-directory
		    lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory)
		  (not
		   addr-range-1
		   ia32e-la-to-pa-page-table-entry-validp)))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-page-directory-2M-pages-with-disjoint-wm-low-64
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  page-directory-entry) 1)
		(disjoint-p
		 (addr-range 8 addr)
		 (addr-range 8 page-directory-entry-addr))
		(integerp addr))

	   (equal (mv-nth
		   1
		   (ia32e-la-to-pa-page-directory
		    lin-addr page-directory-base-addr wp smep nxe r-w-x cpl
		    (wm-low-64 addr val x86)))
		  (mv-nth
		   1
		   (ia32e-la-to-pa-page-directory
		    lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory)
		  (not
		   ia32e-la-to-pa-page-table-entry-validp)))

(defrule mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)

		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  page-directory-entry) 1)

		(equal accessed (ia32e-pde-2MB-page-slice :pde-a page-directory-entry))
		(equal dirty (ia32e-pde-2MB-page-slice :pde-d page-directory-entry))
		(equal accessed-entry
		       (if (equal accessed 0)
			   (!ia32e-pde-2MB-page-slice :pde-a 1 page-directory-entry)
			 page-directory-entry))
		(equal dirty-entry
		       (if (and (equal dirty 0)
				(equal r-w-x :w))
			   (!ia32e-pde-2MB-page-slice :pde-d 1 accessed-entry)
			 accessed-entry))
		(equal dirty-x86
		       (if (or (equal accessed 0)
			       (and (equal dirty 0)
				    (equal r-w-x :w)))
			   (wm-low-64 page-directory-entry-addr dirty-entry x86)
			 x86)))

	   (equal (mv-nth
		   2
		   (ia32e-la-to-pa-page-directory
		    lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86))
		  dirty-x86))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory)
		  (not)))

;; 4K pages:

(defrule mv-nth-0-no-error-ia32e-la-to-pa-page-directory-4K-pages-with-disjoint-!memi
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  page-directory-entry) 0)
		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry)
			    12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))
		(pairwise-disjoint-p-aux
		 (addr-range 1 addr)
		 (translation-governing-addresses-for-page-directory
		  lin-addr page-directory-base-addr x86))
		(integerp addr))
	   (equal (mv-nth
		   0
		   (ia32e-la-to-pa-page-directory
		    lin-addr page-directory-base-addr wp smep nxe r-w-x cpl
		    (xw :mem addr val x86)))
		  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory)
		  (not
		   addr-range-1
		   ia32e-la-to-pa-page-table-entry-validp)))

(defrule mv-nth-0-no-error-ia32e-la-to-pa-page-directory-4K-pages-with-disjoint-wm-low-64
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  page-directory-entry) 0)
		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry)
			    12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))

		(pairwise-disjoint-p-aux
		 (addr-range 8 addr)
		 (translation-governing-addresses-for-page-directory
		  lin-addr page-directory-base-addr x86))
		(integerp addr))
	   (equal (mv-nth
		   0
		   (ia32e-la-to-pa-page-directory
		    lin-addr page-directory-base-addr wp smep nxe r-w-x cpl
		    (wm-low-64 addr val x86)))
		  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory)
		  (not
		   ia32e-la-to-pa-page-table-entry-validp)))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  page-directory-entry) 0))

	   (equal (mv-nth
		   1
		   (ia32e-la-to-pa-page-directory
		    lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86))
		  (mv-nth
		   1
		   (ia32e-la-to-pa-page-table
		    lin-addr
		    (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12)
		    (ia32e-page-tables-slice :u/s page-directory-entry)
		    wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory)
		  (not)))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages-with-disjoint-!memi
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  page-directory-entry) 0)
		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry)
			    12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))
		(pairwise-disjoint-p-aux
		 (addr-range 1 addr)
		 (translation-governing-addresses-for-page-directory
		  lin-addr page-directory-base-addr x86))
		;; (pairwise-disjoint-p-aux
		;;  (addr-range 1 addr)
		;;  (list (addr-range 8 page-directory-entry-addr)
		;;        (addr-range 8 page-table-entry-addr)))
		(integerp addr))

	   (equal (mv-nth
		   1
		   (ia32e-la-to-pa-page-directory
		    lin-addr page-directory-base-addr wp smep nxe r-w-x cpl
		    (xw :mem addr val x86)))
		  (mv-nth
		   1
		   (ia32e-la-to-pa-page-directory
		    lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory)
		  (not
		   mv-nth-1-no-error-ia32e-la-to-pa-page-table
		   addr-range-1
		   ia32e-la-to-pa-page-table-entry-validp)))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages-with-disjoint-wm-low-64
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  page-directory-entry) 0)
		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry)
			    12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))
		(pairwise-disjoint-p-aux
		 (addr-range 8 addr)
		 (translation-governing-addresses-for-page-directory
		  lin-addr page-directory-base-addr x86))
		;; (pairwise-disjoint-p-aux
		;;  (addr-range 8 addr)
		;;  (list (addr-range 8 page-directory-entry-addr)
		;;        (addr-range 8 page-table-entry-addr)))
		(integerp addr))

	   (equal (mv-nth
		   1
		   (ia32e-la-to-pa-page-directory
		    lin-addr page-directory-base-addr wp smep nxe r-w-x cpl
		    (wm-low-64 addr val x86)))
		  (mv-nth
		   1
		   (ia32e-la-to-pa-page-directory
		    lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory)
		  (not
		   ia32e-la-to-pa-page-table-entry-validp)))

(defrule mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  page-directory-entry) 0)

		(equal accessed (ia32e-page-tables-slice :a page-directory-entry))
		(equal accessed-entry
		       (if (equal accessed 0)
			   (!ia32e-page-tables-slice :a 1 page-directory-entry)
			 page-directory-entry)))

	   (equal (mv-nth
		   2
		   (ia32e-la-to-pa-page-directory
		    lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86))
		  (let* ((page-table-x86
			  (mv-nth
			   2
			   (ia32e-la-to-pa-page-table
			    lin-addr
			    (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12)
			    (ia32e-page-tables-slice :u/s page-directory-entry)
			    wp smep nxe r-w-x cpl x86))))
		    (if (equal accessed 0)
			(wm-low-64 page-directory-entry-addr accessed-entry page-table-x86)
		      page-table-x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory)
		  (not
		   ia32e-la-to-pa-page-table-entry-validp)))

;; ......................................................................
;; Reading page-directory-entry-addr again using rm-low-64:
;; ......................................................................

;; 2M pages:

(defruled rm-low-64-and-page-directory-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  page-directory-entry) 1)
		(physical-address-p page-directory-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 page-directory-base-addr) 0)
		(x86p x86))
	   (equal (rm-low-64 page-directory-entry-addr
			     (mv-nth
			      2
			      (ia32e-la-to-pa-page-directory
			       lin-addr page-directory-base-addr wp smep nxe r-w-x
			       cpl x86)))
		  (cond
		   ( ;; Accessed and dirty bits are set.
		    (and (equal (ia32e-page-tables-slice :a page-directory-entry) 1)
			 (equal (ia32e-page-tables-slice :d page-directory-entry) 1))
		    (rm-low-64 page-directory-entry-addr x86))

		   ( ;; Accessed bit is set and dirty bit is clear and
		    ;; memory write is being done.
		    (and (equal (ia32e-page-tables-slice :a page-directory-entry) 1)
			 (equal (ia32e-page-tables-slice :d page-directory-entry) 0)
			 (equal r-w-x :w))
		    (!ia32e-page-tables-slice :d 1 (rm-low-64 page-directory-entry-addr x86)))

		   ( ;; Accessed bit is set and dirty bit is clear and
		    ;; memory write is not being done.
		    (and (equal (ia32e-page-tables-slice :a page-directory-entry) 1)
			 (equal (ia32e-page-tables-slice :d page-directory-entry) 0)
			 (not (equal r-w-x :w)))
		    (rm-low-64 page-directory-entry-addr x86))

		   ( ;; Accessed and dirty bits are clear and memory
		    ;; write is being done.
		    (and (equal (ia32e-page-tables-slice :a page-directory-entry) 0)
			 (equal (ia32e-page-tables-slice :d page-directory-entry) 0)
			 (equal r-w-x :w))
		    (!ia32e-page-tables-slice
		     :d 1
		     (!ia32e-page-tables-slice
		      :a 1
		      (rm-low-64 page-directory-entry-addr x86))))

		   ( ;; Accessed bit and dirty bits are clear and memory
		    ;; write is not being done.
		    (and (equal (ia32e-page-tables-slice :a page-directory-entry) 0)
			 (equal (ia32e-page-tables-slice :d page-directory-entry) 0)
			 (not (equal r-w-x :w)))
		    (!ia32e-page-tables-slice :a 1 (rm-low-64 page-directory-entry-addr x86)))

		   (t
		    ;; This shouldn't be reached.
		    (rm-low-64 page-directory-entry-addr
			       (mv-nth
				2
				(ia32e-la-to-pa-page-directory
				 lin-addr page-directory-base-addr wp smep nxe r-w-x
				 cpl x86)))))))

  :do-not '(preprocess)
  :in-theory (e/d ()
		  (not
		   ia32e-la-to-pa-page-directory-entry-validp
		   ia32e-la-to-pa-page-table-entry-validp
		   unsigned-byte-p
		   signed-byte-p)))

;; 4K pages:

(defruled rm-low-64-and-page-directory-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  page-directory-entry) 0)

		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))
		;; (disjoint-p
		;;  (addr-range 8 page-directory-entry-addr)
		;;  (addr-range 8 page-table-entry-addr))
		(pairwise-disjoint-p
		 (translation-governing-addresses-for-page-directory
		  lin-addr page-directory-base-addr x86))
		(physical-address-p page-directory-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 page-directory-base-addr) 0)
		(x86p x86))

	   (equal (rm-low-64 page-directory-entry-addr
			     (mv-nth
			      2
			      (ia32e-la-to-pa-page-directory
			       lin-addr page-directory-base-addr wp smep nxe r-w-x
			       cpl x86)))
		  (cond
		   ((equal (ia32e-page-tables-slice :a page-directory-entry) 0)
		    (!ia32e-page-tables-slice
		     :a 1 (rm-low-64 page-directory-entry-addr x86)))
		   ((equal (ia32e-page-tables-slice :a page-directory-entry) 1)
		    (rm-low-64 page-directory-entry-addr x86)))))
  :hints (("Goal" :do-not '(preprocess)
	   :in-theory (e/d ()
			   (ia32e-la-to-pa-page-directory-entry-validp
			    not
			    member-p-cons
			    disjoint-p-cons
			    mv-nth-1-no-error-ia32e-la-to-pa-page-table
			    mv-nth-2-no-error-ia32e-la-to-pa-page-table
			    ia32e-la-to-pa-page-table-entry-validp
			    unsigned-byte-p
			    signed-byte-p)))))

;; ......................................................................
;; !memi and state after data structure walk WoW theorem:
;; ......................................................................

;; 2M pages:

(defrule disjoint-!memi-mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  page-directory-entry) 1)

		(disjoint-p
		 (addr-range 1 addr)
		 (addr-range 8 page-directory-entry-addr))
		(integerp addr))
	   (equal
	    (mv-nth
	     2
	     (ia32e-la-to-pa-page-directory
	      lin-addr page-directory-base-addr wp smep nxe r-w-x cpl
	      (xw :mem addr val x86)))
	    (xw :mem
	     addr val
	     (mv-nth
	      2
	      (ia32e-la-to-pa-page-directory
	       lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory)
		  (not
		   addr-range-1)))

;; 4K pages:

(defrule disjoint-!memi-mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  page-directory-entry) 0)

		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))

		;; (pairwise-disjoint-p-aux
		;;  (addr-range 1 addr)
		;;  (list (addr-range 8 page-directory-entry-addr)
		;;        (addr-range 8 page-table-entry-addr)))

		(pairwise-disjoint-p-aux
		 (addr-range 1 addr)
		 (translation-governing-addresses-for-page-directory
		  lin-addr page-directory-base-addr x86))
		(integerp addr))
	   (equal
	    (mv-nth
	     2
	     (ia32e-la-to-pa-page-directory
	      lin-addr page-directory-base-addr wp smep nxe r-w-x cpl
	      (xw :mem addr val x86)))
	    (xw :mem
	     addr val
	     (mv-nth
	      2
	      (ia32e-la-to-pa-page-directory
	       lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory
		   wm-low-64 wm-low-32)
		  (not
		   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-2M-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-table
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   ia32e-la-to-pa-page-table-entry-validp)))

;; ......................................................................
;; Reading addresses disjoint from page-directory-entry-addr after walking
;; the page directory:
;; ......................................................................

;; 2M pages:

(defrule disjoint-memi-read-mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  page-directory-entry) 1)

		(disjoint-p
		 (addr-range 1 addr)
		 (addr-range 8 page-directory-entry-addr)))
	   (equal
	    (xr :mem
	     addr
	     (mv-nth
	      2
	      (ia32e-la-to-pa-page-directory
	       lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)))
	    (xr :mem addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory)
		  (not
		   addr-range-1)))

(defrule disjoint-rm-low-64-read-mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  page-directory-entry) 1)

		(disjoint-p
		 (addr-range 8 addr)
		 (addr-range 8 page-directory-entry-addr))
		(integerp addr))
	   (equal
	    (rm-low-64
	     addr
	     (mv-nth
	      2
	      (ia32e-la-to-pa-page-directory
	       lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)))
	    (rm-low-64 addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory)
		  (not)))

(defrule disjoint-rm-low-32-read-mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  page-directory-entry) 1)

		(disjoint-p
		 (addr-range 4 addr)
		 (addr-range 8 page-directory-entry-addr))
		(integerp addr))
	   (equal
	    (rm-low-32
	     addr
	     (mv-nth
	      2
	      (ia32e-la-to-pa-page-directory
	       lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)))
	    (rm-low-32 addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory
		   wm-low-64)
		  (not)))

;; 4K pages:

(defrule disjoint-memi-read-mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  page-directory-entry) 0)

		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))

		(pairwise-disjoint-p-aux
		 (addr-range 1 addr)
		 (translation-governing-addresses-for-page-directory
		  lin-addr page-directory-base-addr x86)))
	   (equal
	    (xr :mem
	     addr
	     (mv-nth
	      2
	      (ia32e-la-to-pa-page-directory
	       lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)))
	    (xr :mem addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory
		   wm-low-64 wm-low-32)
		  (not
		   disjoint-memi-read-mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
		   disjoint-memi-read-mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
		   disjoint-rm-low-64-read-mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
		   disjoint-rm-low-32-read-mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-table
		   ia32e-la-to-pa-page-table-entry-validp
		   mv-nth-1-no-error-ia32e-la-to-pa-page-table)))

(defrule disjoint-rm-low-64-read-mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  page-directory-entry) 0)

		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))

		(pairwise-disjoint-p-aux
		 (addr-range 8 addr)
		 (translation-governing-addresses-for-page-directory
		  lin-addr page-directory-base-addr x86))

		(integerp addr))
	   (equal
	    (rm-low-64
	     addr
	     (mv-nth
	      2
	      (ia32e-la-to-pa-page-directory
	       lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)))
	    (rm-low-64 addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory)
		  (not
		   disjoint-rm-low-64-read-mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
		   disjoint-rm-low-32-read-mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-table
		   ia32e-la-to-pa-page-table-entry-validp
		   mv-nth-1-no-error-ia32e-la-to-pa-page-table)))

(defrule disjoint-rm-low-32-read-mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  page-directory-entry) 0)

		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))

		(pairwise-disjoint-p-aux
		 (addr-range 4 addr)
		 (translation-governing-addresses-for-page-directory
		  lin-addr page-directory-base-addr x86))

		(integerp addr))
	   (equal
	    (rm-low-32
	     addr
	     (mv-nth
	      2
	      (ia32e-la-to-pa-page-directory
	       lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)))
	    (rm-low-32 addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory
		   wm-low-64)
		  (not
		   disjoint-rm-low-64-read-mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
		   disjoint-rm-low-32-read-mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-table
		   ia32e-la-to-pa-page-table-entry-validp
		   mv-nth-1-no-error-ia32e-la-to-pa-page-table)))

;; ......................................................................
;; Theorems that state that the validity of the page directory entry
;; is preserved when writes are done to disjoint addresses or :a/:d
;; are set:
;; ......................................................................

;; 2M pages:

(defrule page-directory-entry-with-disjoint-!memi-still-valid-ia32e-la-to-pa-page-directory-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  page-directory-entry) 1)

		(disjoint-p (addr-range 1 addr)
			    (addr-range 8 page-directory-entry-addr)))

	   (ia32e-la-to-pa-page-directory-entry-validp
	    lin-addr page-directory-base-addr wp smep nxe r-w-x cpl
	    (xw :mem addr val x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory)
		  (not
		   addr-range-1
		   ia32e-la-to-pa-page-table-entry-validp
		   unsigned-byte-p
		   signed-byte-p)))

(defrule page-directory-entry-with-disjoint-wm-low-64-still-valid-ia32e-la-to-pa-page-directory-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  page-directory-entry) 1)

		(disjoint-p (addr-range 8 addr)
			    (addr-range 8 page-directory-entry-addr))

		(integerp addr)
		(physical-address-p page-directory-base-addr)
		(x86p x86))

	   (ia32e-la-to-pa-page-directory-entry-validp
	    lin-addr page-directory-base-addr wp smep nxe r-w-x cpl
	    (wm-low-64 addr val x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory)
		  (not
		   ia32e-la-to-pa-page-table-entry-validp
		   unsigned-byte-p
		   signed-byte-p)))

(defrule page-directory-entry-with-accessed-bit-set-still-valid-ia32e-la-to-pa-page-directory-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  page-directory-entry) 1)
		(physical-address-p page-directory-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 page-directory-base-addr) 0)
		(x86p x86))

	   (ia32e-la-to-pa-page-directory-entry-validp
	    lin-addr page-directory-base-addr wp smep nxe r-w-x cpl
	    (wm-low-64
	     page-directory-entry-addr
	     ;; (!ia32e-page-tables-slice :a 1 page-directory-entry)
	     (logior 32 (logand 18446744073709551583 page-directory-entry))
	     x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory)
		  (not
		   ia32e-la-to-pa-page-table-entry-validp
		   unsigned-byte-p
		   signed-byte-p)))

(defrule page-directory-entry-with-dirty-bit-set-still-valid-ia32e-la-to-pa-page-directory-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  page-directory-entry) 1)
		(physical-address-p page-directory-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 page-directory-base-addr) 0)
		(x86p x86))

	   (ia32e-la-to-pa-page-directory-entry-validp
	    lin-addr page-directory-base-addr wp smep nxe r-w-x cpl
	    (wm-low-64
	     page-directory-entry-addr
	     ;; (!ia32e-page-tables-slice :d 1 page-directory-entry)
	     (logior 64 (logand 18446744073709551551 page-directory-entry))
	     x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory)
		  (not
		   ia32e-la-to-pa-page-table-entry-validp
		   unsigned-byte-p
		   signed-byte-p)))

(defrule page-directory-entry-with-accessed-and-dirty-bits-set-still-valid-ia32e-la-to-pa-page-directory-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  page-directory-entry) 1)
		(physical-address-p page-directory-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 page-directory-base-addr) 0)
		(x86p x86))

	   (ia32e-la-to-pa-page-directory-entry-validp
	    lin-addr page-directory-base-addr wp smep nxe r-w-x cpl
	    (wm-low-64
	     page-directory-entry-addr
	     ;; (!ia32e-page-tables-slice :d 1 (!ia32e-page-tables-slice :a 1 page-directory-entry))
	     (logior
	      64
	      (logand
	       18446744073709551551
	       (logior 32 (logand 18446744073709551583 page-directory-entry))))
	     x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory)
		  (not
		   ia32e-la-to-pa-page-table-entry-validp
		   unsigned-byte-p
		   signed-byte-p)))

;; 4K pages:

(defrule page-directory-entry-with-accessed-bit-set-still-valid-ia32e-la-to-pa-page-directory-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))
		(pairwise-disjoint-p (translation-governing-addresses-for-page-directory
		  lin-addr page-directory-base-addr x86))
		(physical-address-p page-directory-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 page-directory-base-addr) 0)
		(x86p x86))

	   (ia32e-la-to-pa-page-directory-entry-validp
	    lin-addr page-directory-base-addr wp smep nxe r-w-x cpl
	    (wm-low-64
	     page-directory-entry-addr
	     ;; (!ia32e-page-tables-slice :a 1 page-directory-entry)
	     (logior 32 (logand 18446744073709551583 page-directory-entry))
	     x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory)
		  (not
		   mv-nth-2-no-error-ia32e-la-to-pa-page-table
		   mv-nth-1-no-error-ia32e-la-to-pa-page-table
		   ia32e-la-to-pa-page-table-entry-validp
		   unsigned-byte-p
		   signed-byte-p)))

(defrule page-directory-entry-with-dirty-bit-set-still-valid-ia32e-la-to-pa-page-directory-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))
		(pairwise-disjoint-p (translation-governing-addresses-for-page-directory
		  lin-addr page-directory-base-addr x86))
		(physical-address-p page-directory-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 page-directory-base-addr) 0)
		(x86p x86))

	   (ia32e-la-to-pa-page-directory-entry-validp
	    lin-addr page-directory-base-addr wp smep nxe r-w-x cpl
	    (wm-low-64
	     page-directory-entry-addr
	     ;; (!ia32e-page-tables-slice :d 1 page-directory-entry)
	     (logior 64 (logand 18446744073709551551 page-directory-entry))
	     x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory)
		  (not
		   mv-nth-2-no-error-ia32e-la-to-pa-page-table
		   mv-nth-1-no-error-ia32e-la-to-pa-page-table
		   ia32e-la-to-pa-page-table-entry-validp
		   unsigned-byte-p
		   signed-byte-p)))

(defrule page-directory-entry-with-accessed-and-dirty-bits-set-still-valid-ia32e-la-to-pa-page-directory-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  page-directory-entry) 0)
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))
		(pairwise-disjoint-p (translation-governing-addresses-for-page-directory
				      lin-addr page-directory-base-addr x86))
		(physical-address-p page-directory-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 page-directory-base-addr) 0)
		(x86p x86))

	   (ia32e-la-to-pa-page-directory-entry-validp
	    lin-addr page-directory-base-addr wp smep nxe r-w-x cpl
	    (wm-low-64
	     page-directory-entry-addr
	     ;; (!ia32e-page-tables-slice :d 1 (!ia32e-page-tables-slice :a 1 page-directory-entry))
	     (logior
	      64
	      (logand
	       18446744073709551551
	       (logior 32 (logand 18446744073709551583 page-directory-entry))))
	     x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory)
		  (not
		   ia32e-la-to-pa-page-table-entry-validp
		   mv-nth-2-no-error-ia32e-la-to-pa-page-table
		   mv-nth-1-no-error-ia32e-la-to-pa-page-table
		   unsigned-byte-p
		   signed-byte-p)))


(defrule page-directory-entry-with-disjoint-!memi-still-valid-ia32e-la-to-pa-page-directory-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  page-directory-entry) 0)
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))

		(pairwise-disjoint-p-aux
		 (addr-range 1 addr)
		 (translation-governing-addresses-for-page-directory
		  lin-addr page-directory-base-addr x86))

		(integerp addr)
		(physical-address-p page-directory-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 page-directory-base-addr) 0)
		(x86p x86))

	   (ia32e-la-to-pa-page-directory-entry-validp
	    lin-addr page-directory-base-addr wp smep nxe r-w-x cpl
	    (xw :mem addr val x86)))
  :hints (("Goal" :do-not '(preprocess)
	   :in-theory (e/d ()
			   (ia32e-la-to-pa-page-table-entry-validp
			    mv-nth-2-no-error-ia32e-la-to-pa-page-table
			    mv-nth-1-no-error-ia32e-la-to-pa-page-table
			    not
			    addr-range-1
			    unsigned-byte-p
			    signed-byte-p)))))

(defrule page-directory-entry-with-disjoint-wm-low-64-still-valid-ia32e-la-to-pa-page-directory-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  page-directory-entry) 0)

		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))

		(pairwise-disjoint-p-aux
		 (addr-range 8 addr)
		 (translation-governing-addresses-for-page-directory
		  lin-addr page-directory-base-addr x86))

		(integerp addr)
		(physical-address-p page-directory-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 page-directory-base-addr) 0)
		(x86p x86))

	   (ia32e-la-to-pa-page-directory-entry-validp
	    lin-addr page-directory-base-addr wp smep nxe r-w-x cpl
	    (wm-low-64 addr val x86)))
  :hints (("Goal" :do-not '(preprocess)
	   :in-theory (e/d ()
			   (ia32e-la-to-pa-page-table-entry-validp
			    mv-nth-2-no-error-ia32e-la-to-pa-page-table
			    mv-nth-1-no-error-ia32e-la-to-pa-page-table
			    not
			    unsigned-byte-p
			    signed-byte-p)))))

;; ......................................................................
;; Reading page directory entry from x86 states where :a/:d are set:
;; ......................................................................

;; 2M pages:

(defrule reading-entry-with-accessed-bit-set-ia32e-la-to-pa-page-directory-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  page-directory-entry) 1)
		(physical-address-p page-directory-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 page-directory-base-addr) 0)
		(x86p x86))

	   (equal
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-directory
	      lin-addr page-directory-base-addr wp smep nxe r-w-x cpl
	      (wm-low-64
	       page-directory-entry-addr
	       ;; (!ia32e-page-tables-slice :a 1 page-directory-entry)
	       (logior 32 (logand 18446744073709551583 page-directory-entry))
	       x86)))
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-directory
	      lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d ()
		  (ia32e-la-to-pa-page-directory-entry-validp
		   mv-nth-2-no-error-ia32e-la-to-pa-page-table
		   mv-nth-1-no-error-ia32e-la-to-pa-page-table
		   not
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
		   unsigned-byte-p
		   signed-byte-p)))

(defrule reading-entry-with-dirty-bit-set-ia32e-la-to-pa-page-directory-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  page-directory-entry) 1)
		(physical-address-p page-directory-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 page-directory-base-addr) 0)
		(x86p x86))

	   (equal
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-directory
	      lin-addr page-directory-base-addr wp smep nxe r-w-x cpl
	      (wm-low-64
	       page-directory-entry-addr
	       ;; (!ia32e-page-tables-slice :d 1 page-directory-entry)
	       (logior 64 (logand 18446744073709551551 page-directory-entry))
	       x86)))
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-directory
	      lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d ()
		  (ia32e-la-to-pa-page-directory-entry-validp
		   mv-nth-2-no-error-ia32e-la-to-pa-page-table
		   mv-nth-1-no-error-ia32e-la-to-pa-page-table
		   not
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
		   unsigned-byte-p
		   signed-byte-p)))

(defrule reading-entry-with-accessed-and-dirty-bits-ia32e-la-to-pa-page-directory-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  page-directory-entry) 1)
		(physical-address-p page-directory-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 page-directory-base-addr) 0)
		(x86p x86))

	   (equal
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-directory
	      lin-addr page-directory-base-addr wp smep nxe r-w-x cpl
	      (wm-low-64
	       page-directory-entry-addr
	       ;; (!ia32e-page-tables-slice :d 1 (!ia32e-page-tables-slice :a 1 page-directory-entry))
	       (logior
		64
		(logand
		 18446744073709551551
		 (logior 32 (logand 18446744073709551583 page-directory-entry))))
	       x86)))
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-directory
	      lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d ()
		  (ia32e-la-to-pa-page-directory-entry-validp
		   mv-nth-2-no-error-ia32e-la-to-pa-page-table
		   mv-nth-1-no-error-ia32e-la-to-pa-page-table
		   not
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
		   unsigned-byte-p
		   signed-byte-p)))

;; 4K pages:

(defrule reading-entry-with-accessed-bit-set-ia32e-la-to-pa-page-directory-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  page-directory-entry) 0)
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))
		(pairwise-disjoint-p (translation-governing-addresses-for-page-directory
		  lin-addr page-directory-base-addr x86))
		(physical-address-p page-directory-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 page-directory-base-addr) 0)
		(x86p x86))

	   (equal
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-directory
	      lin-addr page-directory-base-addr wp smep nxe r-w-x cpl
	      (wm-low-64
	       page-directory-entry-addr
	       ;; (!ia32e-page-tables-slice :a 1 page-directory-entry)
	       (logior 32 (logand 18446744073709551583 page-directory-entry))
	       x86)))
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-directory
	      lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d ()
		  (ia32e-la-to-pa-page-directory-entry-validp
		   mv-nth-1-no-error-ia32e-la-to-pa-page-table
		   mv-nth-2-no-error-ia32e-la-to-pa-page-table
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   not
		   unsigned-byte-p
		   signed-byte-p)))

(defrule reading-entry-with-dirty-bit-set-ia32e-la-to-pa-page-directory-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  page-directory-entry) 0)
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))
		(pairwise-disjoint-p (translation-governing-addresses-for-page-directory
		  lin-addr page-directory-base-addr x86))
		(physical-address-p page-directory-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 page-directory-base-addr) 0)
		(x86p x86))

	   (equal
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-directory
	      lin-addr page-directory-base-addr wp smep nxe r-w-x cpl
	      (wm-low-64
	       page-directory-entry-addr
	       ;; (!ia32e-page-tables-slice :d 1 page-directory-entry)
	       (logior 64 (logand 18446744073709551551 page-directory-entry))
	       x86)))
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-directory
	      lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d ()
		  (ia32e-la-to-pa-page-directory-entry-validp
		   mv-nth-1-no-error-ia32e-la-to-pa-page-table
		   mv-nth-2-no-error-ia32e-la-to-pa-page-table
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   not
		   ia32e-la-to-pa-page-table-entry-validp
		   unsigned-byte-p
		   signed-byte-p)))

(defrule reading-entry-with-accessed-and-dirty-bits-set-ia32e-la-to-pa-page-directory-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  page-directory-entry) 0)
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))
		(pairwise-disjoint-p
		 (translation-governing-addresses-for-page-directory
		  lin-addr page-directory-base-addr x86))
		(physical-address-p page-directory-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 page-directory-base-addr) 0)
		(x86p x86))

	   (equal
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-directory
	      lin-addr page-directory-base-addr wp smep nxe r-w-x cpl
	      (wm-low-64
	       page-directory-entry-addr
	       ;; (!ia32e-page-tables-slice :d 1 (!ia32e-page-tables-slice :a 1 page-directory-entry))
	       (logior
		64
		(logand
		 18446744073709551551
		 (logior 32 (logand 18446744073709551583 page-directory-entry))))
	       x86)))
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-directory
	      lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d ()
		  (ia32e-la-to-pa-page-directory-entry-validp
		   mv-nth-1-no-error-ia32e-la-to-pa-page-table
		   mv-nth-2-no-error-ia32e-la-to-pa-page-table
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   not
		   unsigned-byte-p
		   signed-byte-p)))

;; ......................................................................
;; More theorems about preservation of validity of page directory entries:
;; ......................................................................

;; 2M pages:

(defrule relating-validity-of-two-entries-in-two-x86-states-wrt-page-directory-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry-1 (rm-low-64 page-directory-entry-addr x86))
		(equal page-directory-entry-2 (rm-low-64 page-directory-entry-addr x86-another))
		(equal (ia32e-pde-2MB-page-slice :pde-ps page-directory-entry-1) 1)
		(ia32e-la-to-pa-page-directory-entry-components-equal-p
		 '2M page-directory-entry-1 page-directory-entry-2))
	   (ia32e-la-to-pa-page-directory-entry-validp
	    lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86-another))
  :in-theory (e/d
	      (ia32e-la-to-pa-page-directory-entry-components-equal-p)
	      ()))

(defruled page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-page-directory-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  page-directory-entry) 1)
		(physical-address-p page-directory-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 page-directory-base-addr) 0)
		(x86p x86))
	   (ia32e-la-to-pa-page-directory-entry-components-equal-p
	    '2M
	    (rm-low-64 page-directory-entry-addr x86)
	    (rm-low-64
	     page-directory-entry-addr
	     (mv-nth
	      2
	      (ia32e-la-to-pa-page-directory
	       lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)))))
  :hints (("Goal" :do-not '(preprocess)
	   :in-theory (e/d (rm-low-64-and-page-directory-2M-pages
			    ia32e-la-to-pa-page-directory-entry-components-equal-p)
			   (ia32e-la-to-pa-page-directory
			    mv-nth-2-no-error-ia32e-la-to-pa-page-table
			    mv-nth-1-no-error-ia32e-la-to-pa-page-table
			    not
			    member-p-cons
			    disjoint-p-cons
			    unsigned-byte-p
			    signed-byte-p)))))

(defrule re-read-entry-still-valid-ia32e-la-to-pa-page-directory-2M-pages

  ;; To prove this kind of theorem, we need the following kinds of key
  ;; lemmas:

  ;; 1. relating-validity-of-two-entries-in-two-x86-states-wrt-page-directory-2M-pages
  ;; 2. page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-page-directory-2M-pages
  ;;    (to relieve the components hyp in lemma 1).

  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  page-directory-entry) 1)
		(physical-address-p page-directory-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 page-directory-base-addr) 0)
		(x86p x86))
	   (ia32e-la-to-pa-page-directory-entry-validp
	    lin-addr page-directory-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
	    (mv-nth
	     2
	     (ia32e-la-to-pa-page-directory
	      lin-addr page-directory-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
  :do-not '(preprocess)
  :in-theory (e/d (page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-page-directory-2M-pages)
		  (ia32e-la-to-pa-page-directory-entry-validp
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-table
		   mv-nth-1-no-error-ia32e-la-to-pa-page-table
		   not
		   ia32e-la-to-pa-page-table
		   ia32e-la-to-pa-page-table-entry-validp
		   unsigned-byte-p
		   signed-byte-p)))

;; 4K pages:

(defrule relating-validity-of-two-entries-in-two-x86-states-wrt-page-directory-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry-1 (rm-low-64 page-directory-entry-addr x86))
		(equal page-directory-entry-2 (rm-low-64 page-directory-entry-addr x86-another))
		(equal (ia32e-pde-pg-table-slice :pde-ps page-directory-entry-1) 0)
		(ia32e-la-to-pa-page-directory-entry-components-equal-p
		 '4K page-directory-entry-1 page-directory-entry-2)

		(equal page-table-base-addr-1
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry-1) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr-1))

		(equal page-table-entry-1 (rm-low-64 page-table-entry-addr x86))
		(equal page-table-entry-2 (rm-low-64 page-table-entry-addr x86-another))

		(ia32e-la-to-pa-page-table-entry-components-equal-p
		 page-table-entry-1 page-table-entry-2))

	   (ia32e-la-to-pa-page-directory-entry-validp
	    lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86-another))
  :in-theory (e/d
	      (ia32e-la-to-pa-page-directory-entry-components-equal-p)
	      ()))

(defruled page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-page-directory-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  page-directory-entry) 0)

		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))

		(pairwise-disjoint-p (translation-governing-addresses-for-page-directory
				      lin-addr page-directory-base-addr x86))

		(physical-address-p page-directory-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 page-directory-base-addr) 0)
		(x86p x86))

	   (ia32e-la-to-pa-page-directory-entry-components-equal-p
	    '4K
	    (rm-low-64 page-directory-entry-addr x86)
	    (rm-low-64
	     page-directory-entry-addr
	     (mv-nth
	      2
	      (ia32e-la-to-pa-page-directory
	       lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)))))
  :hints (("Goal" :do-not '(preprocess)
	   :in-theory (e/d (rm-low-64-and-page-directory-4K-pages)
			   (ia32e-la-to-pa-page-directory-entry-validp
			    mv-nth-2-no-error-ia32e-la-to-pa-page-table
			    mv-nth-1-no-error-ia32e-la-to-pa-page-table
			    mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
			    not
			    member-p-cons
			    disjoint-p-cons
			    unsigned-byte-p
			    signed-byte-p)))))

(defruled page-table-components-equal-rm-low-64-of-page-table-entry-addr-via-page-directory-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  page-directory-entry) 0)

		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))

		(pairwise-disjoint-p (translation-governing-addresses-for-page-directory
				      lin-addr page-directory-base-addr x86))

		(physical-address-p page-directory-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 page-directory-base-addr) 0)
		(x86p x86))

	   (ia32e-la-to-pa-page-table-entry-components-equal-p
	    (rm-low-64 page-table-entry-addr x86)
	    (rm-low-64
	     page-table-entry-addr
	     (mv-nth
	      2
	      (ia32e-la-to-pa-page-directory
	       lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)))))
  :hints (("Goal" :do-not '(preprocess)
	   :in-theory (e/d (ia32e-la-to-pa-page-table-entry-components-equal-p
			    mv-nth-2-no-error-ia32e-la-to-pa-page-table
			    mv-nth-1-no-error-ia32e-la-to-pa-page-table
			    page-table-components-equal-rm-low-64-of-table-page-table-entry-addr-via-page-table-4K-pages)
			   (ia32e-la-to-pa-page-directory-entry-validp
			    not
			    member-p-cons
			    disjoint-p-cons
			    unsigned-byte-p
			    signed-byte-p)))))

(defrule re-read-entry-still-valid-ia32e-la-to-pa-page-directory-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  page-directory-entry) 0)

		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))
		(pairwise-disjoint-p (translation-governing-addresses-for-page-directory
				      lin-addr page-directory-base-addr x86))
		(physical-address-p page-directory-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 page-directory-base-addr) 0)
		(x86p x86))

	   (ia32e-la-to-pa-page-directory-entry-validp
	    lin-addr page-directory-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
	    (mv-nth
	     2
	     (ia32e-la-to-pa-page-directory
	      lin-addr page-directory-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
  :hints (("Goal" :do-not '(preprocess)
	   :in-theory (e/d
		       (page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-page-directory-4K-pages
			page-table-components-equal-rm-low-64-of-page-table-entry-addr-via-page-directory-4K-pages)
		       (ia32e-la-to-pa-page-directory-entry-validp
			member-p-cons
			disjoint-p-cons
			not
			mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
			unsigned-byte-p
			signed-byte-p)))))

;; ......................................................................
;; Two page table walks --- same addresses:
;; ......................................................................

;; 2M pages:

(defrule two-page-table-walks-ia32e-la-to-pa-page-directory-2M-pages-same-addresses

  ;; Shilpi: A very rough (and possibly imprecise) proof sketch, which
  ;; I'm leaving as a note to myself:

  ;; For primary pages of a data structure (i.e., pages that can be
  ;; accessed directly from the data structure), the two page walks
  ;; theorem needs the following kinds of key lemmas:

  ;; 1. mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2m-pages
  ;; 2. reading-entry-with-accessed-bit-set-ia32e-la-to-pa-page-directory-2m-pages
  ;; 3. reading-entry-with-dirty-bit-set-ia32e-la-to-pa-page-directory-2m-pages
  ;; 4. reading-entry-with-accessed-and-dirty-bits-ia32e-la-to-pa-page-directory-2m-pages

  ;; The x86 state returned by walking the page directory the first
  ;; time (i.e., (mv-nth 2 (ia32e-la-to-pa-page-directory ...))) can
  ;; be described in terms of the initial x86 state, with or without
  ;; the accessed/dirty bits being set. Lemma 1 is used to rewrite
  ;; this state in the LHS of the theorem.  Four cases result from the
  ;; application of lemma 1: one, no modification of page-directory-entry
  ;; (so LHS = RHS); two, :a set in page-directory-entry; three, :d set in
  ;; page-directory-entry; and four, both :a and :d set in page-directory-entry.
  ;; Lemmas 2, 3, and 4 deal with cases two, three, and four, and
  ;; rewrite the LHS to RHS.

  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  page-directory-entry) 1)
		(physical-address-p page-directory-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 page-directory-base-addr) 0)
		(x86p x86))
	   (equal
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-directory
	      lin-addr page-directory-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
	      (mv-nth
	       2
	       (ia32e-la-to-pa-page-directory
		lin-addr page-directory-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-directory
	      lin-addr page-directory-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
	      x86))))
  :do-not '(preprocess)
  :in-theory (e/d ()
		  (ia32e-la-to-pa-page-directory-entry-validp
		   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-2m-pages
		   mv-nth-1-no-error-ia32e-la-to-pa-page-table
		   mv-nth-2-no-error-ia32e-la-to-pa-page-table
		   member-p-cons
		   disjoint-p-cons
		   not
		   unsigned-byte-p
		   signed-byte-p)))

(defrule two-page-table-walks-ia32e-la-to-pa-page-directory-2M-pages-same-entry-different-addrs

  ;; Because of equality-of-page-directory-entry-addr,
  ;; page-directory-entry-addr-1 and page-directory-entry-addr-2 (and
  ;; thus, page-directory-entry-1 and page-directory-entry-2) are
  ;; equal.

  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr-1 page-directory-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr-2 page-directory-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
		(equal page-directory-entry-addr-1
		       (page-directory-entry-addr
			lin-addr-1 page-directory-base-addr))
		(equal page-directory-entry-1
		       (rm-low-64 page-directory-entry-addr-1 x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry-1) 1)
		(equal (part-select lin-addr-1 :low 21 :high 29)
		       (part-select lin-addr-2 :low 21 :high 29))
		(not (equal (part-select lin-addr-1 :low 0 :width 21)
			    (part-select lin-addr-2 :low 0 :width 21)))
		(physical-address-p page-directory-base-addr)
		(canonical-address-p lin-addr-1)
		(canonical-address-p lin-addr-2)
		(equal (loghead 12 page-directory-base-addr) 0)
		(x86p x86))
	   (equal
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-directory
	      lin-addr-1 page-directory-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
	      (mv-nth
	       2
	       (ia32e-la-to-pa-page-directory
		lin-addr-2 page-directory-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-directory
	      lin-addr-1 page-directory-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
	      x86))))
  :use ((:instance equality-of-page-directory-entry-addr))
  :do-not '(preprocess)
  :in-theory (e/d ()
		  (ia32e-la-to-pa-page-directory-entry-validp
		   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-2m-pages
		   mv-nth-1-no-error-ia32e-la-to-pa-page-table
		   mv-nth-2-no-error-ia32e-la-to-pa-page-table
		   member-p-cons
		   disjoint-p-cons
		   not
		   unsigned-byte-p
		   signed-byte-p)))

;; 4K pages:

(defruled page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-page-table-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  page-directory-entry) 0)

		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))


		(pairwise-disjoint-p (translation-governing-addresses-for-page-directory
				      lin-addr page-directory-base-addr x86))

		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal u-s-acc (ia32e-page-tables-slice :u/s
							page-directory-entry))

		(physical-address-p page-directory-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 page-directory-base-addr) 0)
		(x86p x86))

	   (ia32e-la-to-pa-page-directory-entry-components-equal-p
	    '4K
	    (rm-low-64 page-directory-entry-addr x86)
	    (rm-low-64
	     page-directory-entry-addr
	     (mv-nth
	      2
	      (ia32e-la-to-pa-page-table
	       lin-addr page-table-base-addr u-s-acc
	       wp smep nxe r-w-x cpl x86)))))
  :hints (("Goal" :do-not '(preprocess)
	   :in-theory (e/d
		       (ia32e-la-to-pa-page-directory-entry-components-equal-p)
		       (ia32e-la-to-pa-page-directory-entry-validp
			not
			member-p-cons
			disjoint-p-cons
			ia32e-la-to-pa-page-table-entry-validp
			unsigned-byte-p
			signed-byte-p)))))

(defrule re-read-entry-still-page-directory-valid-page-table-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  page-directory-entry) 0)

		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal u-s-acc (ia32e-page-tables-slice :u/s page-directory-entry))

		(pairwise-disjoint-p (translation-governing-addresses-for-page-directory
				      lin-addr page-directory-base-addr x86))

		(physical-address-p page-directory-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 page-directory-base-addr) 0)
		(x86p x86))

	   (ia32e-la-to-pa-page-directory-entry-validp
	    lin-addr page-directory-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
	    (mv-nth
	     2
	     (ia32e-la-to-pa-page-table
	      lin-addr page-table-base-addr u-s-acc wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))

  :hints (("Goal" :do-not '(preprocess)
	   :use ((:instance re-read-entry-still-valid-ia32e-la-to-pa-page-directory-4K-pages))
	   :in-theory (e/d
		       (page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-page-table-4K-pages
			page-table-components-equal-rm-low-64-of-table-page-table-entry-addr-via-page-table-4K-pages)
		       (re-read-entry-still-valid-ia32e-la-to-pa-page-directory-4K-pages
			ia32e-la-to-pa-page-directory-entry-validp
			member-p-cons
			disjoint-p-cons
			not
			mv-nth-2-no-error-ia32e-la-to-pa-page-table
			mv-nth-1-no-error-ia32e-la-to-pa-page-table
			unsigned-byte-p
			signed-byte-p)))))

(defrule two-page-table-walks-ia32e-la-to-pa-page-directory-4K-pages-same-addresses

  ;; Shilpi: A very rough (and possibly imprecise) proof sketch, which
  ;; I'm leaving as a note to myself:

  ;; For secondary pages of a data structure (i.e., the pages that
  ;; have to be accessed after one level of indirection), the two page
  ;; walks theorem needs the following kinds of key lemmas:

  ;; 1. mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
  ;; 2. re-read-entry-still-page-directory-valid-page-table-4K-pages
  ;; 3. reading-entry-with-accessed-bit-set-ia32e-la-to-pa-page-directory-4K-pages
  ;; 4. reading-entry-with-dirty-bit-set-ia32e-la-to-pa-page-directory-4K-pages
  ;; 5. reading-entry-with-accessed-and-dirty-bits-set-ia32e-la-to-pa-page-directory-4K-pages
  ;; 6. mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
  ;; 7. page-directory-entry-validp-to-page-table-entry-validp
  ;; 8. two-page-table-walks-ia32e-la-to-pa-page-table-same-addresses

  ;; The x86 state returned by walking the page directory the first
  ;; time (i.e., (mv-nth 2 (ia32e-la-to-pa-page-directory ...))) can
  ;; be described in terms of the x86 state returned after walking the
  ;; page table (i.e., (mv-nth 2 (ia32e-la-to-pa-page-table ...))),
  ;; with or without the accessed/dirty bits being set.  Lemma 1
  ;; rewrites this state in the LHS of the theorem.  Lemma 2
  ;; establishes that the state returned after walking the page table
  ;; satisfies ia32e-la-to-pa-page-directory-entry-validp, and lemmas
  ;; 3, 4, and 5 will rewrite the LHS to the following form:

  ;; (mv-nth 1 (ia32e-la-to-pa-page-directory ....
  ;;           (mv-nth 2 (ia32e-la-to-pa-page-table ...)))

  ;; Using lemmas 2 and 6, the above form will be re-written to:

  ;; (mv-nth 1 (ia32e-la-to-pa-page-table ....
  ;;           (mv-nth 2 (ia32e-la-to-pa-page-table ...)))

  ;; and lemmas 7 and 8 will re-write this to (mv-nth 1
  ;; (ia32e-la-to-pa-page-table ....).

  ;; Lemma 6 will rewrite the RHS to match this LHS.

  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)

		(pairwise-disjoint-p
		 (translation-governing-addresses-for-page-directory
		  lin-addr page-directory-base-addr x86))

		(physical-address-p page-directory-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 page-directory-base-addr) 0)
		(x86p x86))

	   (equal
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-directory
	      lin-addr page-directory-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
	      (mv-nth
	       2
	       (ia32e-la-to-pa-page-directory
		lin-addr page-directory-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-directory
	      lin-addr page-directory-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
	      x86))))
  :do-not '(preprocess)
  :in-theory (e/d
	      ()
	      (ia32e-la-to-pa-page-directory-entry-validp
	       mv-nth-1-no-error-ia32e-la-to-pa-page-table
	       mv-nth-2-no-error-ia32e-la-to-pa-page-table
	       member-p-cons
	       disjoint-p-cons
	       not
	       unsigned-byte-p
	       signed-byte-p)))

(defruled page-directory-entry-equal-rm-low-64-of-page-directory-entry-addr-via-page-table-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr-1 page-directory-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr-2 page-directory-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
		(equal page-directory-entry-addr-1
		       (page-directory-entry-addr lin-addr-1 page-directory-base-addr))
		(equal page-directory-entry-1 (rm-low-64 page-directory-entry-addr-1 x86))
		(equal (ia32e-page-tables-slice :ps  page-directory-entry-1) 0)

		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry-1) 12))
		(equal u-s-acc (ia32e-page-tables-slice :u/s page-directory-entry-1))

		(pairwise-disjoint-p
		 (translation-governing-addresses-for-page-directory
		  lin-addr-1 page-directory-base-addr x86))

		;; So that page directory entries are the same...
		(equal (part-select lin-addr-1 :low 21 :high 29)
		       (part-select lin-addr-2 :low 21 :high 29))
		;; So that page table entries are the same...
		(equal (part-select lin-addr-1 :low 12 :high 20)
		       (part-select lin-addr-2 :low 12 :high 20))
		;; So that the physical address is different...
		(not (equal (part-select lin-addr-1 :low 0 :width 12)
			    (part-select lin-addr-2 :low 0 :width 12)))
		(physical-address-p page-directory-base-addr)
		(canonical-address-p lin-addr-1)
		(canonical-address-p lin-addr-2)
		(equal (loghead 12 page-directory-base-addr) 0)
		(x86p x86))

	   (equal
	    (rm-low-64
	     page-directory-entry-addr-1
	     (mv-nth
	      2
	      (ia32e-la-to-pa-page-table
	       lin-addr-2 page-table-base-addr
	       u-s-acc wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)))
	    (rm-low-64 page-directory-entry-addr-1 x86)))
  :hints (("Goal" :do-not '(preprocess)
	   :use ((:instance equality-of-page-directory-entry-addr)
		 (:instance equality-of-page-table-entry-addr))
	   :in-theory (e/d
		       (ia32e-la-to-pa-page-directory-entry-components-equal-p)
		       (ia32e-la-to-pa-page-directory-entry-validp
			not
			member-p-cons
			disjoint-p-cons
			ia32e-la-to-pa-page-table-entry-validp
			unsigned-byte-p
			signed-byte-p)))))

(defrule re-read-entry-still-page-directory-valid-page-table-4K-pages-same-entry-different-addrs
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr-1 page-directory-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr-2 page-directory-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
		(equal page-directory-entry-addr-1
		       (page-directory-entry-addr lin-addr-1 page-directory-base-addr))
		(equal page-directory-entry-1 (rm-low-64 page-directory-entry-addr-1 x86))
		(equal (ia32e-page-tables-slice :ps  page-directory-entry-1) 0)

		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry-1) 12))
		(equal u-s-acc (ia32e-page-tables-slice :u/s page-directory-entry-1))

		(pairwise-disjoint-p
		 (translation-governing-addresses-for-page-directory
		  lin-addr-1 page-directory-base-addr x86))

		;; So that page directory entries are the same...
		(equal (part-select lin-addr-1 :low 21 :high 29)
		       (part-select lin-addr-2 :low 21 :high 29))
		;; So that page table entries are the same...
		(equal (part-select lin-addr-1 :low 12 :high 20)
		       (part-select lin-addr-2 :low 12 :high 20))
		;; So that the physical address is different...
		(not (equal (part-select lin-addr-1 :low 0 :width 12)
			    (part-select lin-addr-2 :low 0 :width 12)))
		(physical-address-p page-directory-base-addr)
		(canonical-address-p lin-addr-1)
		(canonical-address-p lin-addr-2)
		(equal (loghead 12 page-directory-base-addr) 0)
		(x86p x86))

	   (ia32e-la-to-pa-page-directory-entry-validp
	    lin-addr-1 page-directory-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
	    (mv-nth
	     2
	     (ia32e-la-to-pa-page-table
	      lin-addr-2 page-table-base-addr u-s-acc wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))

  :hints (("Goal" :do-not '(preprocess)
	   :use ((:instance equality-of-page-directory-entry-addr)
		 (:instance equality-of-page-table-entry-addr))
	   :in-theory (e/d
		       (ia32e-la-to-pa-page-directory-entry-components-equal-p
			page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-page-table-4K-pages
			page-table-components-equal-rm-low-64-of-table-page-table-entry-addr-via-page-table-4K-pages
			page-directory-entry-equal-rm-low-64-of-page-directory-entry-addr-via-page-table-4K-pages
			re-read-entry-still-valid-ia32e-la-to-pa-page-directory-4K-pages)
		       (ia32e-la-to-pa-page-directory-entry-validp
			not
			member-p-cons
			disjoint-p-cons
			ia32e-la-to-pa-page-table-entry-validp
			unsigned-byte-p
			signed-byte-p)))))

(defrule two-page-table-walks-ia32e-la-to-pa-page-directory-4K-pages-same-entry-different-addrs

  ;; Because of equality-of-page-directory-entry-addr,
  ;; page-directory-entry-addr-1 and page-directory-entry-addr-2 (and
  ;; thus, page-directory-entry-1 and page-directory-entry-2) are
  ;; equal.

  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr-1 page-directory-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr-2 page-directory-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
		(equal page-directory-entry-addr-1
		       (page-directory-entry-addr
			lin-addr-1 page-directory-base-addr))
		(equal page-directory-entry-1
		       (rm-low-64 page-directory-entry-addr-1 x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry-1) 0)

		(pairwise-disjoint-p
		 (translation-governing-addresses-for-page-directory
		  lin-addr-1 page-directory-base-addr x86))

		;; So that page directory entries are the same...
		(equal (part-select lin-addr-1 :low 21 :high 29)
		       (part-select lin-addr-2 :low 21 :high 29))
		;; So that page table entries are the same...
		(equal (part-select lin-addr-1 :low 12 :high 20)
		       (part-select lin-addr-2 :low 12 :high 20))
		;; So that the physical address is different...
		(not (equal (part-select lin-addr-1 :low 0 :width 12)
			    (part-select lin-addr-2 :low 0 :width 12)))
		(physical-address-p page-directory-base-addr)
		(canonical-address-p lin-addr-1)
		(canonical-address-p lin-addr-2)
		(equal (loghead 12 page-directory-base-addr) 0)
		(x86p x86))

	   (equal
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-directory
	      lin-addr-1 page-directory-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
	      (mv-nth
	       2
	       (ia32e-la-to-pa-page-directory
		lin-addr-2 page-directory-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-directory
	      lin-addr-1 page-directory-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
	      x86))))
  :use ((:instance equality-of-page-directory-entry-addr))
  :do-not '(preprocess)
  :in-theory (e/d (equality-of-page-table-entry-addr
		   page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-page-table-4K-pages
		   page-directory-entry-equal-rm-low-64-of-page-directory-entry-addr-via-page-table-4K-pages)
		  (ia32e-la-to-pa-page-directory-entry-validp
		   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-2M-pages
		   mv-nth-1-no-error-ia32e-la-to-pa-page-table
		   mv-nth-2-no-error-ia32e-la-to-pa-page-table
		   member-p-cons
		   disjoint-p-cons
		   not
		   unsigned-byte-p
		   signed-byte-p)))

;; ......................................................................
;; Two page table walks --- different entries:
;; ......................................................................

(defrule two-page-table-walks-ia32e-la-to-pa-page-directory-different-entries

  ;; Key lemmas:

  ;; mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2m-pages
  ;; mv-nth-1-no-error-ia32e-la-to-pa-page-directory-2m-pages-with-disjoint-wm-low-64
  ;; mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4k-pages
  ;; mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4k-pages-with-disjoint-wm-low-64

  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr-1 page-directory-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr-2 page-directory-base-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)

		(pairwise-disjoint-p
		 (append
		  (translation-governing-addresses-for-page-directory
		   lin-addr-2 page-directory-base-addr-2 x86)
		  (translation-governing-addresses-for-page-directory
		   lin-addr-1 page-directory-base-addr-1 x86)))

		(physical-address-p page-directory-base-addr-1)
		(canonical-address-p lin-addr-1)
		(equal (loghead 12 page-directory-base-addr-1) 0)

		(physical-address-p page-directory-base-addr-2)
		(canonical-address-p lin-addr-2)
		(equal (loghead 12 page-directory-base-addr-2) 0)

		(x86p x86))
	   (equal
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-directory
	      lin-addr-1 page-directory-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
	      (mv-nth
	       2
	       (ia32e-la-to-pa-page-directory
		lin-addr-2 page-directory-base-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-directory
	      lin-addr-1 page-directory-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
	      x86))))
  :do-not '(preprocess)
  :cases ((and (equal (ia32e-page-tables-slice :ps
					       (rm-low-64 (part-install (part-select lin-addr-1 :low 21 :high 29)
									page-directory-base-addr-1
									:low 3 :high 11)
							  x86))
		      1)
	       (equal (ia32e-page-tables-slice :ps
					       (rm-low-64 (part-install (part-select lin-addr-2 :low 21 :high 29)
									page-directory-base-addr-2
									:low 3 :high 11) x86))
		      1))

	  (and (equal (ia32e-page-tables-slice :ps
					       (rm-low-64 (part-install (part-select lin-addr-1 :low 21 :high 29)
									page-directory-base-addr-1
									:low 3 :high 11)
							  x86))
		      1)
	       (equal (ia32e-page-tables-slice :ps
					       (rm-low-64 (part-install (part-select lin-addr-2 :low 21 :high 29)
									page-directory-base-addr-2
									:low 3 :high 11) x86))
		      0))

	  (and (equal (ia32e-page-tables-slice :ps
					       (rm-low-64 (part-install (part-select lin-addr-1 :low 21 :high 29)
									page-directory-base-addr-1
									:low 3 :high 11)
							  x86))
		      0)
	       (equal (ia32e-page-tables-slice :ps
					       (rm-low-64 (part-install (part-select lin-addr-2 :low 21 :high 29)
									page-directory-base-addr-2
									:low 3 :high 11) x86))
		      1))

	  (and (equal (ia32e-page-tables-slice :ps
					       (rm-low-64 (part-install (part-select lin-addr-1 :low 21 :high 29)
									page-directory-base-addr-1
									:low 3 :high 11)
							  x86))
		      0)
	       (equal (ia32e-page-tables-slice :ps
					       (rm-low-64 (part-install (part-select lin-addr-2 :low 21 :high 29)
									page-directory-base-addr-2
									:low 3 :high 11) x86))
		      0)))
  :in-theory (e/d ()
		  (ia32e-la-to-pa-page-directory-entry-validp
		   mv-nth-1-no-error-ia32e-la-to-pa-page-table
		   mv-nth-2-no-error-ia32e-la-to-pa-page-table
		   member-p-cons
		   disjoint-p-cons
		   not
		   unsigned-byte-p
		   signed-byte-p)))

;; ......................................................................
;; More theorems about validity of page directory entries being
;; preserved when the translation-governing addresses are disjoint:
;; ......................................................................

(defrule validity-preserved-same-x86-state-disjoint-addresses-wrt-page-directory
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr-1 page-directory-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr-2 page-directory-base-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)

		(pairwise-disjoint-p
		 (append
		  (translation-governing-addresses-for-page-directory
		   lin-addr-2 page-directory-base-addr-2 x86)
		  (translation-governing-addresses-for-page-directory
		   lin-addr-1 page-directory-base-addr-1 x86)))

		(physical-address-p page-directory-base-addr-1)
		(canonical-address-p lin-addr-1)
		(equal (loghead 12 page-directory-base-addr-1) 0)

		(physical-address-p page-directory-base-addr-2)
		(canonical-address-p lin-addr-2)
		(equal (loghead 12 page-directory-base-addr-2) 0)

		(x86p x86))

	   (ia32e-la-to-pa-page-directory-entry-validp
	    lin-addr-1 page-directory-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
	    (mv-nth 2 (ia32e-la-to-pa-page-directory
		       lin-addr-2 page-directory-base-addr-2
		       wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))

  :cases ((and (equal (ia32e-page-tables-slice :ps
					       (rm-low-64 (part-install (part-select lin-addr-1 :low 21 :high 29)
									page-directory-base-addr-1
									:low 3 :high 11)
							  x86))
		      1)
	       (equal (ia32e-page-tables-slice :ps
					       (rm-low-64 (part-install (part-select lin-addr-2 :low 21 :high 29)
									page-directory-base-addr-2
									:low 3 :high 11) x86))
		      1))

	  (and (equal (ia32e-page-tables-slice :ps
					       (rm-low-64 (part-install (part-select lin-addr-1 :low 21 :high 29)
									page-directory-base-addr-1
									:low 3 :high 11)
							  x86))
		      1)
	       (equal (ia32e-page-tables-slice :ps
					       (rm-low-64 (part-install (part-select lin-addr-2 :low 21 :high 29)
									page-directory-base-addr-2
									:low 3 :high 11) x86))
		      0))

	  (and (equal (ia32e-page-tables-slice :ps
					       (rm-low-64 (part-install (part-select lin-addr-1 :low 21 :high 29)
									page-directory-base-addr-1
									:low 3 :high 11)
							  x86))
		      0)
	       (equal (ia32e-page-tables-slice :ps
					       (rm-low-64 (part-install (part-select lin-addr-2 :low 21 :high 29)
									page-directory-base-addr-2
									:low 3 :high 11) x86))
		      1))

	  (and (equal (ia32e-page-tables-slice :ps
					       (rm-low-64 (part-install (part-select lin-addr-1 :low 21 :high 29)
									page-directory-base-addr-1
									:low 3 :high 11)
							  x86))
		      0)
	       (equal (ia32e-page-tables-slice :ps
					       (rm-low-64 (part-install (part-select lin-addr-2 :low 21 :high 29)
									page-directory-base-addr-2
									:low 3 :high 11) x86))
		      0)))

  :in-theory (e/d ()
		  (ia32e-la-to-pa-page-directory-entry-validp
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   member-p-cons
		   disjoint-p-cons
		   not
		   unsigned-byte-p
		   signed-byte-p)))

;; ......................................................................
;; Translation-Governing-Addresses-For-Page-Directory and
;; ia32e-la-to-pa-page-directory-entry:
;; ......................................................................

(defrule translation-governing-addresses-for-page-directory-and-ia32e-la-to-pa-page-directory-pairwise-disjoint
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr-2 page-directory-base-addr-2 wp-2
		 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
		(pairwise-disjoint-p
		 (append
		  (translation-governing-addresses-for-page-directory
		   lin-addr-2 page-directory-base-addr-2 x86)
		  (translation-governing-addresses-for-page-directory
		   lin-addr-1 page-directory-base-addr-1 x86))))
	   (equal
	    (translation-governing-addresses-for-page-directory
	     lin-addr-1 page-directory-base-addr-1
	     (mv-nth 2
		     (ia32e-la-to-pa-page-directory
		      lin-addr-2 page-directory-base-addr-2
		      wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)))
	    (translation-governing-addresses-for-page-directory
	     lin-addr-1 page-directory-base-addr-1 x86)))
  :in-theory (e/d ()
		  (ia32e-la-to-pa-page-directory-entry-validp
		   addr-range-1
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
		   member-p-cons
		   disjoint-p-cons
		   not
		   unsigned-byte-p
		   signed-byte-p)))

(defrule translation-governing-addresses-for-page-directory-and-ia32e-la-to-pa-page-directory-same-addr-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp
		 smep nxe r-w-x cpl x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)
		(physical-address-p page-directory-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 page-directory-base-addr) 0)
		(x86p x86))
	   (equal
	    (translation-governing-addresses-for-page-directory
	     lin-addr page-directory-base-addr
	     (mv-nth 2
		     (ia32e-la-to-pa-page-directory
		      lin-addr page-directory-base-addr
		      wp smep nxe r-w-x cpl x86)))
	    (translation-governing-addresses-for-page-directory
	     lin-addr page-directory-base-addr x86)))
  :in-theory (e/d ()
		  (ia32e-la-to-pa-page-directory-entry-validp
		   addr-range-1
		   member-p-cons
		   disjoint-p-cons
		   not
		   unsigned-byte-p
		   signed-byte-p)))

(defrule translation-governing-addresses-for-page-directory-and-wm-low-64-disjoint-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp
		 smep nxe r-w-x cpl x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)
		(pairwise-disjoint-p-aux
		 (addr-range 8 addr)
		 (translation-governing-addresses-for-page-directory
		  lin-addr page-directory-base-addr x86))
		(integerp addr)
		(physical-address-p page-directory-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 page-directory-base-addr) 0)
		(x86p x86))
	   (equal
	    (translation-governing-addresses-for-page-directory
	     lin-addr page-directory-base-addr
	     (wm-low-64 addr val x86))
	    (translation-governing-addresses-for-page-directory
	     lin-addr page-directory-base-addr x86)))
  :in-theory (e/d ()
		  (ia32e-la-to-pa-page-directory-entry-validp
		   addr-range-1
		   member-p-cons
		   disjoint-p-cons
		   not
		   unsigned-byte-p
		   signed-byte-p)))

(defrule translation-governing-addresses-for-page-directory-and-ia32e-la-to-pa-page-directory-same-addr-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp
		 smep nxe r-w-x cpl x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))

		(pairwise-disjoint-p (translation-governing-addresses-for-page-directory
				      lin-addr page-directory-base-addr x86))

		(physical-address-p page-directory-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 page-directory-base-addr) 0)
		(x86p x86))
	   (equal
	    (translation-governing-addresses-for-page-directory
	     lin-addr page-directory-base-addr
	     (mv-nth 2
		     (ia32e-la-to-pa-page-directory
		      lin-addr page-directory-base-addr
		      wp smep nxe r-w-x cpl x86)))
	    (translation-governing-addresses-for-page-directory
	     lin-addr page-directory-base-addr x86)))
  :in-theory (e/d ()
		  (ia32e-la-to-pa-page-directory-entry-validp
		   addr-range-1
		   member-p-cons
		   disjoint-p-cons
		   not
		   unsigned-byte-p
		   signed-byte-p)))

(defrule translation-governing-addresses-for-page-directory-and-wm-low-64-disjoint-4K-page
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp
		 smep nxe r-w-x cpl x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))

		(pairwise-disjoint-p
		 (translation-governing-addresses-for-page-directory
		  lin-addr page-directory-base-addr x86))
		(pairwise-disjoint-p-aux
		 (addr-range 8 addr)
		 (translation-governing-addresses-for-page-directory
		  lin-addr page-directory-base-addr x86))

		(integerp addr)
		(physical-address-p page-directory-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 page-directory-base-addr) 0)
		(x86p x86))
	   (equal
	    (translation-governing-addresses-for-page-directory
	     lin-addr page-directory-base-addr
	     (wm-low-64 addr val x86))
	    (translation-governing-addresses-for-page-directory
	     lin-addr page-directory-base-addr x86)))
  :in-theory (e/d ()
		  (ia32e-la-to-pa-page-directory-entry-validp
		   addr-range-1
		   member-p-cons
		   disjoint-p-cons
		   not
		   unsigned-byte-p
		   signed-byte-p)))

(in-theory (e/d () (ia32e-la-to-pa-page-directory-entry-validp)))

;; ======================================================================

;; ia32e-la-to-pa-page-dir-ptr-table:

(defmacro ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p-1G-body
  (entry-1 entry-2)
  `(and (equal (ia32e-pdpte-1GB-page-slice :pdpte-p ,entry-1)
	       (ia32e-pdpte-1GB-page-slice :pdpte-p ,entry-2))
	(equal (ia32e-pdpte-1GB-page-slice :pdpte-r/w ,entry-1)
	       (ia32e-pdpte-1GB-page-slice :pdpte-r/w ,entry-2))
	(equal (ia32e-pdpte-1GB-page-slice :pdpte-u/s ,entry-1)
	       (ia32e-pdpte-1GB-page-slice :pdpte-u/s ,entry-2))
	(equal (ia32e-pdpte-1GB-page-slice :pdpte-ps ,entry-1)
	       (ia32e-pdpte-1GB-page-slice :pdpte-ps ,entry-2))
	(equal (ia32e-pdpte-1GB-page-slice :pdpte-xd ,entry-1)
	       (ia32e-pdpte-1GB-page-slice :pdpte-xd ,entry-2))
	;; Reserved bits are zero.
	;; (equal (loghead 11 (logtail 52 ,entry-2)) 0)
	;; (equal (loghead 17 (logtail 13 ,entry-2)) 0)
	(equal (loghead 11 (logtail 52 ,entry-1))
	       (loghead 11 (logtail 52 ,entry-2)))
	(equal (loghead 17 (logtail 13 ,entry-1))
	       (loghead 17 (logtail 13 ,entry-2)))))

(defmacro ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p-4K-or-2M-body
  (entry-1 entry-2)
  `(and (equal (ia32e-pdpte-pg-dir-slice :pdpte-p ,entry-1)
	       (ia32e-pdpte-pg-dir-slice :pdpte-p ,entry-2))
	(equal (ia32e-pdpte-pg-dir-slice :pdpte-r/w ,entry-1)
	       (ia32e-pdpte-pg-dir-slice :pdpte-r/w ,entry-2))
	(equal (ia32e-pdpte-pg-dir-slice :pdpte-u/s ,entry-1)
	       (ia32e-pdpte-pg-dir-slice :pdpte-u/s ,entry-2))
	(equal (ia32e-pdpte-pg-dir-slice :pdpte-ps ,entry-1)
	       (ia32e-pdpte-pg-dir-slice :pdpte-ps ,entry-2))
	(equal (ia32e-pdpte-pg-dir-slice :pdpte-pd ,entry-1)
	       (ia32e-pdpte-pg-dir-slice :pdpte-pd ,entry-2))
	(equal (ia32e-pdpte-pg-dir-slice :pdpte-xd ,entry-1)
	       (ia32e-pdpte-pg-dir-slice :pdpte-xd ,entry-2))
	;; Reserved bits are zero.
	;; (equal (loghead 11 (logtail 52 ,entry-2)) 0)
	(equal (loghead 11 (logtail 52 ,entry-1))
	       (loghead 11 (logtail 52 ,entry-2)))))

(define ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
  (page-size? entry-1 entry-2)
  :verify-guards nil
  :non-executable t
  (if (equal page-size? '1G)
      (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p-1G-body
       entry-1 entry-2)
    (if (equal page-size? '4K-or-2M)
	(ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p-4K-or-2M-body
	 entry-1 entry-2)
      't)))

(defmacro ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p-1G-macro (x y)
  `(ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p-1G-body ,x ,y))

(defmacro ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p-4K-or-2M-macro (x y)
  `(ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p-4K-or-2M-body
  ,x ,y))

(defthm ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p-reflexive
  (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p a b b)
  :hints (("Goal" :in-theory (e/d
			      (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p)
			      ()))))

(defthm ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p-accessed-bit-set
  (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
   a b (logior 32 (logand 18446744073709551583 b)))
  :hints (("Goal" :in-theory (e/d
			      (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p)
			      ()))))

(defthm ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p-dirty-bit-set
  (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
   a b (logior 64 (logand 18446744073709551551 b)))
  :hints (("Goal" :in-theory (e/d
			      (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p)
			      ()))))

(defthm ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p-accessed-and-dirty-bits-set
  (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
   a b (logior
	64
	(logand
	 18446744073709551551
	 (logior 32 (logand 18446744073709551583 b)))))
  :hints (("Goal" :in-theory (e/d
			      (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p)
			      ()))))

;; ......................................................................
;; Establishing inferior data structure entry validity from page
;; directory pointer table entry's validity:
;; ......................................................................

(defrule page-dir-ptr-entry-validp-to-page-directory-entry-validp
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps ptr-table-entry) 0)
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry)
			    12)))
	   (ia32e-la-to-pa-page-directory-entry-validp
	    lin-addr page-directory-base-addr
	    wp smep nxe r-w-x cpl x86)))

(defrule page-dir-ptr-entry-validp-to-page-table-entry-validp
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)a
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal u-s-acc (ia32e-page-tables-slice :u/s page-directory-entry)))
	   (ia32e-la-to-pa-page-table-entry-validp
	    lin-addr page-table-base-addr u-s-acc wp smep nxe r-w-x cpl x86)))

;; ......................................................................
;; Rules about the three return values of
;; ia32e-la-to-pa-page-dir-ptr-table:
;; ......................................................................

(defrule mv-nth-0-no-error-ia32e-la-to-pa-page-dir-ptr-table
  :parents (reasoning-about-page-tables)
  (implies (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
	    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
	   (equal (mv-nth
		   0
		   (ia32e-la-to-pa-page-dir-ptr-table
		    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86))
		  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
		  (not)))

;; 1G pages:

(defrule mv-nth-0-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages-with-disjoint-!memi
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)
		(disjoint-p (addr-range 1 addr)
			    (addr-range 8 ptr-table-entry-addr))
		(integerp addr))
	   (equal (mv-nth
		   0
		   (ia32e-la-to-pa-page-dir-ptr-table
		    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
		    (xw :mem addr val x86)))
		  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
		  (not
		   addr-range-1)))

(defrule mv-nth-0-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages-with-disjoint-wm-low-64
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)
		(disjoint-p (addr-range 8 addr)
			    (addr-range 8 ptr-table-entry-addr))
		(integerp addr))
	   (equal (mv-nth
		   0
		   (ia32e-la-to-pa-page-dir-ptr-table
		    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
		    (wm-low-64 addr val x86)))
		  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
		  (not)))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1))
	   (equal (mv-nth
		   1
		   (ia32e-la-to-pa-page-dir-ptr-table
		    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86))
		  (part-install
		   (part-select lin-addr :low 0 :high 29)
		   (ash (ia32e-pdpte-1GB-page-slice :pdpte-page ptr-table-entry) 30)
		   :low 0 :high 29)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
		  (not)))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages-with-disjoint-!memi
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)
		(disjoint-p (addr-range 1 addr)
			    (addr-range 8 ptr-table-entry-addr))
		(integerp addr))
	   (equal (mv-nth
		   1
		   (ia32e-la-to-pa-page-dir-ptr-table
		    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
		    (xw :mem addr val x86)))
		  (mv-nth
		   1
		   (ia32e-la-to-pa-page-dir-ptr-table
		    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
		  (not
		   addr-range-1)))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages-with-disjoint-wm-low-64
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps ptr-table-entry) 1)
		(disjoint-p (addr-range 8 addr)
			    (addr-range 8 ptr-table-entry-addr))
		(integerp addr))
	   (equal (mv-nth
		   1
		   (ia32e-la-to-pa-page-dir-ptr-table
		    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
		    (wm-low-64 addr val x86)))
		  (mv-nth
		   1
		   (ia32e-la-to-pa-page-dir-ptr-table
		    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
		  (not)))

(defrule mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps ptr-table-entry) 1)
		(equal accessed (ia32e-pdpte-1GB-page-slice :pdpte-a ptr-table-entry))
		(equal dirty (ia32e-pdpte-1GB-page-slice :pdpte-d ptr-table-entry))
		(equal accessed-entry
		       (if (equal accessed 0)
			   (!ia32e-page-tables-slice :a 1 ptr-table-entry)
			 ptr-table-entry))
		(equal dirty-entry
		       (if (and (equal dirty 0)
				(equal r-w-x :w))
			   (!ia32e-pdpte-1GB-page-slice :pdpte-d 1 accessed-entry)
			 accessed-entry)))
	   (equal (mv-nth
		   2
		   (ia32e-la-to-pa-page-dir-ptr-table
		    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86))
		  (if (or (equal accessed 0)
			  (and (equal dirty 0)
			       (equal r-w-x :w)))
		      (wm-low-64 ptr-table-entry-addr dirty-entry x86)
		    x86)))

  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
		  (not
		   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages)))

;; 2M pages:

(defrule mv-nth-0-no-error-ia32e-la-to-pa-page-dir-ptr-table-2M-pages-with-disjoint-!memi
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)
		(pairwise-disjoint-p-aux
		 (addr-range 1 addr)
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))
		(integerp addr))
	   (equal (mv-nth
		   0
		   (ia32e-la-to-pa-page-dir-ptr-table
		    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
		    (xw :mem addr val x86)))
		  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
		  (not
		   addr-range-1)))

(defrule mv-nth-0-no-error-ia32e-la-to-pa-page-dir-ptr-table-2M-pages-with-disjoint-wm-low-64
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)
		(pairwise-disjoint-p-aux
		 (addr-range 8 addr)
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))
		(integerp addr))
	   (equal (mv-nth
		   0
		   (ia32e-la-to-pa-page-dir-ptr-table
		    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
		    (wm-low-64 addr val x86)))
		  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
		  (not)))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps ptr-table-entry) 0))
	   (equal (mv-nth
		   1
		   (ia32e-la-to-pa-page-dir-ptr-table
		    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86))
		  (mv-nth
		   1
		   (ia32e-la-to-pa-page-directory
		    lin-addr
		    (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12)
		    wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
		  (not)))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-2M-pages-with-disjoint-!memi
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)
		(pairwise-disjoint-p-aux
		 (addr-range 1 addr)
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))
		(integerp addr))
	   (equal (mv-nth
		   1
		   (ia32e-la-to-pa-page-dir-ptr-table
		    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
		    (xw :mem addr val x86)))
		  (mv-nth
		   1
		   (ia32e-la-to-pa-page-dir-ptr-table
		    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
		  (not
		   addr-range-1)))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-2M-pages-with-disjoint-wm-low-64
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)
		(pairwise-disjoint-p-aux
		 (addr-range 8 addr)
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))
		(integerp addr))
	   (equal (mv-nth
		   1
		   (ia32e-la-to-pa-page-dir-ptr-table
		    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
		    (wm-low-64 addr val x86)))
		  (mv-nth
		   1
		   (ia32e-la-to-pa-page-dir-ptr-table
		    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
		  (not)))


(defrule mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps ptr-table-entry) 0)
		(equal accessed (ia32e-page-tables-slice :a ptr-table-entry))
		(equal accessed-entry (if (equal accessed 0)
					  (!ia32e-page-tables-slice :a 1 ptr-table-entry)
					ptr-table-entry)))
	   (equal (mv-nth
		   2
		   (ia32e-la-to-pa-page-dir-ptr-table
		    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86))
		  (let* ((page-dir-x86
			  (mv-nth
			   2
			   (ia32e-la-to-pa-page-directory
			    lin-addr
			    (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12)
			    wp smep nxe r-w-x cpl x86)))
			 (accessed-x86
			  (if (equal accessed 0)
			      (wm-low-64 ptr-table-entry-addr accessed-entry page-dir-x86)
			    page-dir-x86)))
		    accessed-x86)))

  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
		  (not
		   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages)))

;; 4K pages:

(defrule mv-nth-0-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-pages-with-disjoint-!memi
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))
		(pairwise-disjoint-p-aux
		 (addr-range 1 addr)
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))
		(integerp addr))
	   (equal (mv-nth
		   0
		   (ia32e-la-to-pa-page-dir-ptr-table
		    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
		    (xw :mem addr val x86)))
		  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
		  (not
		   addr-range-1)))

(defrule mv-nth-0-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-pages-with-disjoint-wm-low-64
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)a
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))
		(pairwise-disjoint-p-aux
		 (addr-range 8 addr)
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))
		(integerp addr))
	   (equal (mv-nth
		   0
		   (ia32e-la-to-pa-page-dir-ptr-table
		    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
		    (wm-low-64 addr val x86)))
		  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
		  (not)))


(defrule mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-pages-with-disjoint-!memi
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))
		(pairwise-disjoint-p-aux
		 (addr-range 1 addr)
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))
		(integerp addr))
	   (equal (mv-nth
		   1
		   (ia32e-la-to-pa-page-dir-ptr-table
		    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
		    (xw :mem addr val x86)))
		  (mv-nth
		   1
		   (ia32e-la-to-pa-page-dir-ptr-table
		    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
		  (not
		   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   addr-range-1)))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-pages-with-disjoint-wm-low-64
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))
		(pairwise-disjoint-p-aux
		 (addr-range 8 addr)
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))
		(integerp addr))
	   (equal (mv-nth
		   1
		   (ia32e-la-to-pa-page-dir-ptr-table
		    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
		    (wm-low-64 addr val x86)))
		  (mv-nth
		   1
		   (ia32e-la-to-pa-page-dir-ptr-table
		    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
		  (not
		   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages)))

;; ......................................................................
;; Reading page-dir-ptr-table-entry-addr again using rm-low-64:
;; ......................................................................

;; 1G pages:

(defruled rm-low-64-and-page-dir-ptr-table-1G-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps ptr-table-entry) 1)
		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))
	   (equal (rm-low-64 ptr-table-entry-addr
			     (mv-nth
			      2
			      (ia32e-la-to-pa-page-dir-ptr-table
			       lin-addr ptr-table-base-addr wp smep nxe r-w-x
			       cpl x86)))
		  (cond
		   ( ;; Accessed and dirty bits are set.
		    (and (equal (ia32e-page-tables-slice :a ptr-table-entry) 1)
			 (equal (ia32e-page-tables-slice :d ptr-table-entry) 1))
		    (rm-low-64 ptr-table-entry-addr x86))

		   ( ;; Accessed bit is set and dirty bit is clear and
		    ;; memory write is being done.
		    (and (equal (ia32e-page-tables-slice :a ptr-table-entry) 1)
			 (equal (ia32e-page-tables-slice :d ptr-table-entry) 0)
			 (equal r-w-x :w))
		    (!ia32e-page-tables-slice :d 1 (rm-low-64 ptr-table-entry-addr x86)))

		   ( ;; Accessed bit is set and dirty bit is clear and
		    ;; memory write is not being done.
		    (and (equal (ia32e-page-tables-slice :a ptr-table-entry) 1)
			 (equal (ia32e-page-tables-slice :d ptr-table-entry) 0)
			 (not (equal r-w-x :w)))
		    (rm-low-64 ptr-table-entry-addr x86))

		   ( ;; Accessed and dirty bits are clear and memory
		    ;; write is being done.
		    (and (equal (ia32e-page-tables-slice :a ptr-table-entry) 0)
			 (equal (ia32e-page-tables-slice :d ptr-table-entry) 0)
			 (equal r-w-x :w))
		    (!ia32e-page-tables-slice
		     :d 1
		     (!ia32e-page-tables-slice
		      :a 1
		      (rm-low-64 ptr-table-entry-addr x86))))

		   ( ;; Accessed bit and dirty bits are clear and memory
		    ;; write is not being done.
		    (and (equal (ia32e-page-tables-slice :a ptr-table-entry) 0)
			 (equal (ia32e-page-tables-slice :d ptr-table-entry) 0)
			 (not (equal r-w-x :w)))
		    (!ia32e-page-tables-slice :a 1 (rm-low-64 ptr-table-entry-addr x86)))

		   (t
		    ;; This shouldn't be reached.
		    (rm-low-64 ptr-table-entry-addr
			       (mv-nth
				2
				(ia32e-la-to-pa-page-dir-ptr-table
				 lin-addr ptr-table-base-addr wp smep nxe r-w-x
				 cpl x86)))))))

  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
		  (not
		   unsigned-byte-p
		   signed-byte-p
		   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages)))

;; 2M pages:

(defruled rm-low-64-and-page-dir-ptr-table-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))

		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)

		;; (disjoint-p
		;;  (addr-range 8 ptr-table-entry-addr)
		;;  (addr-range 8 page-directory-entry-addr))
		(pairwise-disjoint-p
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))
		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))

	   (equal (rm-low-64 ptr-table-entry-addr
			     (mv-nth
			      2
			      (ia32e-la-to-pa-page-dir-ptr-table
			       lin-addr ptr-table-base-addr wp smep nxe r-w-x
			       cpl x86)))
		  (cond
		   ((equal (ia32e-page-tables-slice :a ptr-table-entry) 0)
		    (!ia32e-page-tables-slice :a 1 ptr-table-entry))
		   ((equal (ia32e-page-tables-slice :a ptr-table-entry) 1)
		    ptr-table-entry))))

  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
		  (not
		   unsigned-byte-p
		   signed-byte-p
		   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages)))

;; 4K pages:

(defruled rm-low-64-and-page-dir-ptr-table-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))

		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)

		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))
		(pairwise-disjoint-p
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))
		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))

	   (equal (rm-low-64 ptr-table-entry-addr
			     (mv-nth
			      2
			      (ia32e-la-to-pa-page-dir-ptr-table
			       lin-addr ptr-table-base-addr wp smep nxe r-w-x
			       cpl x86)))
		  (cond
		   ((equal (ia32e-page-tables-slice :a ptr-table-entry) 0)
		    (!ia32e-page-tables-slice :a 1 ptr-table-entry))
		   ((equal (ia32e-page-tables-slice :a ptr-table-entry) 1)
		    ptr-table-entry))))

  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
		  (disjoint-p-cons
		   member-p-cons
		   not
		   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
		   unsigned-byte-p
		   signed-byte-p
		   acl2::mv-nth-cons-meta)))

;; ......................................................................
;; !memi and state after data structure walk WoW theorem:
;; ......................................................................

;; 1G pages:

(defrule disjoint-!memi-mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

		(disjoint-p
		 (addr-range 1 addr)
		 (addr-range 8 ptr-table-entry-addr))
		(integerp addr))
	   (equal
	    (mv-nth
	     2
	     (ia32e-la-to-pa-page-dir-ptr-table
	      lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
	      (xw :mem addr val x86)))
	    (xw :mem addr val
		   (mv-nth
		    2
		    (ia32e-la-to-pa-page-dir-ptr-table
		     lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
		  (not
		   addr-range-1
		   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages)))

;; 2M pages:

(defrule disjoint-!memi-mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))

		(pairwise-disjoint-p-aux
		 (addr-range 1 addr)
		 (list (addr-range 8 ptr-table-entry-addr)
		       (addr-range 8 page-directory-entry-addr)))

		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)
		(integerp addr))
	   (equal
	    (mv-nth
	     2
	     (ia32e-la-to-pa-page-dir-ptr-table
	      lin-addr ptr-table-base-addr wp smep nxe
	      r-w-x cpl (xw :mem addr val x86)))
	    (xw :mem addr val
		   (mv-nth
		    2
		    (ia32e-la-to-pa-page-dir-ptr-table
		     lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
		  (not
		   addr-range-1
		   ia32e-la-to-pa-page-directory-entry-validp
		   ia32e-la-to-pa-page-table-entry-validp
		   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages)))

;; 4K pages:

(defrule disjoint-!memi-mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))

		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)

		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))

		(pairwise-disjoint-p-aux
		 (addr-range 1 addr)
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))
		(integerp addr))
	   (equal
	    (mv-nth
	     2
	     (ia32e-la-to-pa-page-dir-ptr-table
	      lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
	      (xw :mem addr val x86)))
	    (xw :mem
	     addr val
	     (mv-nth
	      2
	      (ia32e-la-to-pa-page-dir-ptr-table
	       lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table
		   wm-low-64 wm-low-32)
		  (not
		   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages)))

;; ......................................................................
;; Reading addresses disjoint from page-dir-ptr-table-entry-addr after
;; walking the page directory pointer table:
;; ......................................................................

;; 1G pages:

(defrule disjoint-memi-read-mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

		(disjoint-p
		 (addr-range 1 addr)
		 (addr-range 8 ptr-table-entry-addr)))
	   (equal
	    (xr :mem addr
		  (mv-nth
		   2
		   (ia32e-la-to-pa-page-dir-ptr-table
		    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)))
	    (xr :mem addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
		  (not
		   addr-range-1
		   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages)))

(defrule disjoint-rm-low-64-read-mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

		(disjoint-p
		 (addr-range 8 addr)
		 (addr-range 8 ptr-table-entry-addr))
		(integerp addr))
	   (equal
	    (rm-low-64 addr
		       (mv-nth
			2
			(ia32e-la-to-pa-page-dir-ptr-table
			 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)))
	    (rm-low-64 addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
		  (not
		   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages)))

(defrule disjoint-rm-low-32-read-mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

		(disjoint-p
		 (addr-range 4 addr)
		 (addr-range 8 ptr-table-entry-addr))
		(integerp addr))
	   (equal
	    (rm-low-32 addr
		       (mv-nth
			2
			(ia32e-la-to-pa-page-dir-ptr-table
			 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)))
	    (rm-low-32 addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table
		   wm-low-64)
		  (not
		   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages)))

;; 2M pages:

(defrule disjoint-memi-read-mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))

		(pairwise-disjoint-p-aux
		 (addr-range 1 addr)
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))

		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1))
	   (equal
	    (xr :mem addr
		  (mv-nth
		   2
		   (ia32e-la-to-pa-page-dir-ptr-table
		    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)))
	    (xr :mem addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
		  (not
		   addr-range-1
		   ia32e-la-to-pa-page-directory-entry-validp
		   ia32e-la-to-pa-page-table-entry-validp
		   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages)))

(defrule disjoint-rm-low-64-read-mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))

		(pairwise-disjoint-p-aux
		 (addr-range 8 addr)
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))

		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)
		(integerp addr))
	   (equal
	    (rm-low-64 addr
		       (mv-nth
			2
			(ia32e-la-to-pa-page-dir-ptr-table
			 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)))
	    (rm-low-64 addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
		  (not
		   ia32e-la-to-pa-page-directory-entry-validp
		   ia32e-la-to-pa-page-table-entry-validp
		   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages)))

(defrule disjoint-rm-low-32-read-mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))

		(pairwise-disjoint-p-aux
		 (addr-range 4 addr)
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)
		(integerp addr))
	   (equal
	    (rm-low-32 addr
		       (mv-nth
			2
			(ia32e-la-to-pa-page-dir-ptr-table
			 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)))
	    (rm-low-32 addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table
		   wm-low-64)
		  (not
		   ia32e-la-to-pa-page-directory-entry-validp
		   ia32e-la-to-pa-page-table-entry-validp
		   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages)))

;; 4K pages:

(defrule disjoint-memi-read-mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))

		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)

		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))

		(pairwise-disjoint-p-aux
		 (addr-range 1 addr)
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86)))
	   (equal
	    (xr :mem
	     addr
	     (mv-nth
	      2
	      (ia32e-la-to-pa-page-dir-ptr-table
	       lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)))
	    (xr :mem addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table
		   wm-low-64 wm-low-32 ifix)
		  (not
		   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages)))

(defrule disjoint-rm-low-64-read-mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))

		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)

		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))

		(pairwise-disjoint-p-aux
		 (addr-range 8 addr)
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))
		(integerp addr))
	   (equal
	    (rm-low-64
	     addr
	     (mv-nth
	      2
	      (ia32e-la-to-pa-page-dir-ptr-table
	       lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)))
	    (rm-low-64 addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
		  (not
		   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages)))

(defrule disjoint-rm-low-32-read-mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))

		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)

		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))

		(pairwise-disjoint-p-aux
		 (addr-range 4 addr)
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))
		(integerp addr))
	   (equal
	    (rm-low-32 addr
		       (mv-nth
			2
			(ia32e-la-to-pa-page-dir-ptr-table
			 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)))
	    (rm-low-32 addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table
		   wm-low-64)
		  (not
		   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages)))

;; ......................................................................
;; Theorems that state that the validity of the page directory pointer
;; table entry is preserved when writes are done to disjoint addresses
;; or :a/:d are set:
;; ......................................................................

;; 1G pages:

(defrule entry-with-disjoint-!memi-still-valid-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)
		(disjoint-p (addr-range 1 addr)
			    (addr-range 8 ptr-table-entry-addr))
		(integerp addr)
		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))
	   (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
	    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
	    (xw :mem addr val x86)))
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
		  (not
		   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   addr-range-1
		   unsigned-byte-p
		   signed-byte-p)))

(defrule entry-with-disjoint-wm-low-64-still-valid-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)
		(disjoint-p (addr-range 8 addr)
			    (addr-range 8 ptr-table-entry-addr))
		(integerp addr)
		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))
	   (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
	    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
	    (wm-low-64 addr val x86)))
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
		  (not
		   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   unsigned-byte-p
		   signed-byte-p)))

(defrule entry-with-accessed-bit-set-still-valid-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)
		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))
	   (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
	    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
	    (wm-low-64
	     ptr-table-entry-addr
	     ;; (!ia32e-page-tables-slice :a 1 ptr-table-entry)
	     (logior 32 (logand 18446744073709551583 ptr-table-entry))
	     x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
		  (mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   not
		   unsigned-byte-p
		   signed-byte-p)))

(defrule entry-with-dirty-bit-set-still-valid-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)
		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))
	   (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
	    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
	    (wm-low-64
	     ptr-table-entry-addr
	     ;; (!ia32e-page-tables-slice :d 1 ptr-table-entry)
	     (logior 64 (logand 18446744073709551551 ptr-table-entry))
	     x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
		  (mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   not
		   unsigned-byte-p
		   signed-byte-p)))

(defrule entry-with-accessed-and-dirty-bits-set-still-valid-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)
		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))
	   (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
	    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
	    (wm-low-64
	     ptr-table-entry-addr
	     ;; (!ia32e-page-tables-slice :d 1 (!ia32e-page-tables-slice :a 1 ptr-table-entry))
	     (logior
	      64
	      (logand
	       18446744073709551551
	       (logior 32 (logand 18446744073709551583 ptr-table-entry))))
	     x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
		  (mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   not
		   unsigned-byte-p
		   signed-byte-p)))

;; 2M pages:

(defrule entry-with-disjoint-!memi-still-valid-ia32e-la-to-pa-page-dir-ptr-table-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)
		(pairwise-disjoint-p-aux
		 (addr-range 1 addr)
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))
		(integerp addr)
		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))
	   (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
	    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
	    (xw :mem addr val x86)))
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
		  (mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   not
		   addr-range-1
		   unsigned-byte-p
		   signed-byte-p)))

(defrule entry-with-disjoint-wm-low-64-still-valid-ia32e-la-to-pa-page-dir-ptr-table-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)
		(pairwise-disjoint-p-aux
		 (addr-range 8 addr)
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))
		(integerp addr)
		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))
	   (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
	    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
	    (wm-low-64 addr val x86)))
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
		  (mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   not
		   unsigned-byte-p
		   signed-byte-p)))

(defrule entry-with-accessed-bit-set-still-valid-ia32e-la-to-pa-page-dir-ptr-table-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)
		;; (disjoint-p
		;;  (addr-range 8 ptr-table-entry-addr)
		;;  (addr-range 8 page-directory-entry-addr))
		(pairwise-disjoint-p
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))
		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))
	   (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
	    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
	    (wm-low-64
	     ptr-table-entry-addr
	     ;; (!ia32e-page-tables-slice :a 1 ptr-table-entry)
	     (logior 32 (logand 18446744073709551583 ptr-table-entry))
	     x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
		  (mv-nth-1-no-error-ia32e-la-to-pa-page-directory-2M-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
		   not
		   unsigned-byte-p
		   signed-byte-p)))

(defrule entry-with-dirty-bit-set-still-valid-ia32e-la-to-pa-page-dir-ptr-table-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)
		;; (disjoint-p
		;;  (addr-range 8 ptr-table-entry-addr)
		;;  (addr-range 8 page-directory-entry-addr))
		(pairwise-disjoint-p
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))
		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))
	   (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
	    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
	    (wm-low-64
	     ptr-table-entry-addr
	     ;; (!ia32e-page-tables-slice :d 1 ptr-table-entry)
	     (logior 64 (logand 18446744073709551551 ptr-table-entry))
	     x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
		  (mv-nth-1-no-error-ia32e-la-to-pa-page-directory-2M-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
		   not
		   unsigned-byte-p
		   signed-byte-p)))

(defrule entry-with-accessed-and-dirty-bits-set-still-valid-ia32e-la-to-pa-page-dir-ptr-table-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)
		;; (disjoint-p
		;;  (addr-range 8 ptr-table-entry-addr)
		;;  (addr-range 8 page-directory-entry-addr))
		(pairwise-disjoint-p
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))
		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))
	   (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
	    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
	    (wm-low-64
	     ptr-table-entry-addr
	     ;; (!ia32e-page-tables-slice :d 1 (!ia32e-page-tables-slice :a 1 ptr-table-entry))
	     (logior
	      64
	      (logand
	       18446744073709551551
	       (logior 32 (logand 18446744073709551583 ptr-table-entry))))
	     x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
		  (mv-nth-1-no-error-ia32e-la-to-pa-page-directory-2M-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
		   not
		   unsigned-byte-p
		   signed-byte-p)))

;; 4K pages:

(defrule entry-with-disjoint-!memi-still-valid-ia32e-la-to-pa-page-dir-ptr-table-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))

		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)

		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))

		(pairwise-disjoint-p-aux
		 (addr-range 1 addr)
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))
		(integerp addr)

		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))
	   (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
	    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
	    (xw :mem addr val x86)))
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
		  (mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   not
		   addr-range-1
		   unsigned-byte-p
		   signed-byte-p)))

(defrule entry-with-disjoint-wm-low-64-still-valid-ia32e-la-to-pa-page-dir-ptr-table-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))

		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)

		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))

		(pairwise-disjoint-p-aux
		 (addr-range 8 addr)
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))
		(integerp addr)

		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))
	   (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
	    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
	    (wm-low-64 addr val x86)))
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
		  (mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   not
		   unsigned-byte-p
		   signed-byte-p)))

(defrule entry-with-accessed-bit-set-still-valid-ia32e-la-to-pa-page-dir-ptr-table-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))

		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)

		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))

		(pairwise-disjoint-p
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))
		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))
	   (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
	    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
	    (wm-low-64
	     ptr-table-entry-addr
	     ;; (!ia32e-page-tables-slice :a 1 ptr-table-entry)
	     (logior 32 (logand 18446744073709551583 ptr-table-entry))
	     x86)))
  :do-not '(preprocess)
  :in-theory (e/d ()
		  (not
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   unsigned-byte-p
		   signed-byte-p)))

(defrule entry-with-dirty-bit-set-still-valid-ia32e-la-to-pa-page-dir-ptr-table-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))

		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)

		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))

		(pairwise-disjoint-p
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))
		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))
	   (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
	    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
	    (wm-low-64
	     ptr-table-entry-addr
	     ;; (!ia32e-page-tables-slice :d 1 ptr-table-entry)
	     (logior 64 (logand 18446744073709551551 ptr-table-entry))
	     x86)))
  :do-not '(preprocess)
  :in-theory (e/d ()
		  (mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   not
		   unsigned-byte-p
		   signed-byte-p)))

(defrule entry-with-accessed-and-dirty-bits-set-still-valid-ia32e-la-to-pa-page-dir-ptr-table-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))

		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)

		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))

		(pairwise-disjoint-p
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))
		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))
	   (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
	    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
	    (wm-low-64
	     ptr-table-entry-addr
	     ;; (!ia32e-page-tables-slice :d 1 (!ia32e-page-tables-slice :a 1 ptr-table-entry))
	     (logior
	      64
	      (logand
	       18446744073709551551
	       (logior 32 (logand 18446744073709551583 ptr-table-entry))))
	     x86)))
  :do-not '(preprocess)
  :in-theory (e/d ()
		  (mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   not
		   unsigned-byte-p
		   signed-byte-p)))

;; ......................................................................
;; Reading page directory pointer table entry from x86 states where
;; :a/:d are set:
;; ......................................................................

;; 1G pages:

(defrule reading-entry-with-accessed-bit-set-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)
		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))
	   (equal
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-dir-ptr-table
	      lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
	      (wm-low-64
	       ptr-table-entry-addr
	       ;; (!ia32e-page-tables-slice :a 1 ptr-table-entry)
	       (logior 32 (logand 18446744073709551583 ptr-table-entry))
	       x86)))
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-dir-ptr-table
	      lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d ()
		  (mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
		   not
		   unsigned-byte-p
		   signed-byte-p)))

(defrule reading-entry-with-dirty-bit-set-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)
		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))
	   (equal
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-dir-ptr-table
	      lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
	      (wm-low-64
	       ptr-table-entry-addr
	       ;; (!ia32e-page-tables-slice :d 1 ptr-table-entry)
	       (logior 64 (logand 18446744073709551551 ptr-table-entry))
	       x86)))
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-dir-ptr-table
	      lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d ()
		  (mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   not
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
		   unsigned-byte-p
		   signed-byte-p)))

(defrule reading-entry-with-accessed-and-dirty-bits-set-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)
		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))
	   (equal
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-dir-ptr-table
	      lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
	      (wm-low-64
	       ptr-table-entry-addr
	       ;; (!ia32e-page-tables-slice :d 1 (!ia32e-page-tables-slice :a 1 ptr-table-entry))
	       (logior
		64
		(logand
		 18446744073709551551
		 (logior 32 (logand 18446744073709551583 ptr-table-entry))))
	       x86)))
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-dir-ptr-table
	      lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d ()
		  (mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   not
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
		   unsigned-byte-p
		   signed-byte-p)))

;; 2M pages:

(defrule reading-entry-with-accessed-bit-set-ia32e-la-to-pa-page-dir-ptr-table-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)
		;; (disjoint-p
		;;  (addr-range 8 ptr-table-entry-addr)
		;;  (addr-range 8 page-directory-entry-addr))
		(pairwise-disjoint-p
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))
		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))
	   (equal
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-dir-ptr-table
	      lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
	      (wm-low-64
	       ptr-table-entry-addr
	       ;; (!ia32e-page-tables-slice :a 1 ptr-table-entry)
	       (logior 32 (logand 18446744073709551583 ptr-table-entry))
	       x86)))
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-dir-ptr-table
	      lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d ()
		  (mv-nth-1-no-error-ia32e-la-to-pa-page-directory-2M-pages
		   not
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
		   unsigned-byte-p
		   signed-byte-p)))

(defrule reading-entry-with-dirty-bit-set-ia32e-la-to-pa-page-dir-ptr-table-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)
		;; (disjoint-p
		;;  (addr-range 8 ptr-table-entry-addr)
		;;  (addr-range 8 page-directory-entry-addr))
		(pairwise-disjoint-p
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))
		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))
	   (equal
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
	      lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
	      (wm-low-64
	       ptr-table-entry-addr
	       ;; (!ia32e-page-tables-slice :d 1 ptr-table-entry)
	       (logior 64 (logand 18446744073709551551 ptr-table-entry))
	       x86)))
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
	      lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-dir-ptr-table)
		  (not
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
		   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-2M-pages
		   unsigned-byte-p
		   signed-byte-p)))

(defrule reading-entry-with-accessed-and-dirty-bits-set-ia32e-la-to-pa-page-dir-ptr-table-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)
		;; (disjoint-p
		;;  (addr-range 8 ptr-table-entry-addr)
		;;  (addr-range 8 page-directory-entry-addr))
		(pairwise-disjoint-p
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))
		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))
	   (equal
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
	      lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
	      (wm-low-64
	       ptr-table-entry-addr
	       ;; (!ia32e-page-tables-slice :d 1 (!ia32e-page-tables-slice :a 1 ptr-table-entry))
	       (logior
		64
		(logand
		 18446744073709551551
		 (logior 32 (logand 18446744073709551583 ptr-table-entry))))
	       x86)))
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
	      lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d ()
		  (not
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
		   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-2M-pages
		   unsigned-byte-p
		   signed-byte-p)))

;; 4K pages:

(defrule reading-entry-with-accessed-bit-set-ia32e-la-to-pa-page-dir-ptr-table-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))

		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)

		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))

		(pairwise-disjoint-p
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))
		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))
	   (equal
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-dir-ptr-table
	      lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
	      (wm-low-64
	       ptr-table-entry-addr
	       ;; (!ia32e-page-tables-slice :a 1 ptr-table-entry)
	       (logior 32 (logand 18446744073709551583 ptr-table-entry))
	       x86)))
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-dir-ptr-table
	      lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
	      x86))))
  :do-not '(preprocess)
  :in-theory (e/d ()
		  (not
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
		   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-2M-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
		   unsigned-byte-p
		   signed-byte-p)))

(defrule reading-entry-with-dirty-bit-set-ia32e-la-to-pa-page-dir-ptr-table-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))

		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)

		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))

		(pairwise-disjoint-p
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))
		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))
	   (equal
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-dir-ptr-table
	      lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
	      (wm-low-64
	       ptr-table-entry-addr
	       ;; (!ia32e-page-tables-slice :d 1 ptr-table-entry)
	       (logior 64 (logand 18446744073709551551 ptr-table-entry))
	       x86)))
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-dir-ptr-table
	      lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d ()
		  (not
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
		   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-2M-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
		   unsigned-byte-p
		   signed-byte-p)))

(defrule reading-entry-with-accessed-and-dirty-bits-set-ia32e-la-to-pa-page-dir-ptr-table-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))

		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))

		(pairwise-disjoint-p
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))
		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))
	   (equal
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-dir-ptr-table
	      lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl
	      (wm-low-64
	       ptr-table-entry-addr
	       ;; (!ia32e-page-tables-slice :d 1 (!ia32e-page-tables-slice :a 1 ptr-table-entry))
	       (logior
		64
		(logand
		 18446744073709551551
		 (logior 32 (logand 18446744073709551583 ptr-table-entry))))
	       x86)))
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-dir-ptr-table
	      lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d ()
		  (not
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
		   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-2M-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
		   unsigned-byte-p
		   signed-byte-p)))

;; ......................................................................
;; More theorems about preservation of validity of page directory
;; pointer table entries:
;; ......................................................................

;; 1G pages:

(defrule relating-validity-of-two-entries-in-two-x86-states-wrt-page-dir-ptr-table-1G-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal entry-1 (rm-low-64 ptr-table-entry-addr x86))
		(equal entry-2 (rm-low-64 ptr-table-entry-addr x86-another))
		(equal (ia32e-page-tables-slice :ps entry-1) 1)
		(ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
		 '1G entry-1 entry-2))

	   (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
	    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86-another))
  :in-theory (e/d
	      (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p)
	      ()))

(defruled page-dir-ptr-table-components-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-dir-ptr-table-1G-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)
		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))
	   (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
	    '1G
	    (rm-low-64 ptr-table-entry-addr x86)
	    (rm-low-64 ptr-table-entry-addr
		       (mv-nth
			2
			(ia32e-la-to-pa-page-dir-ptr-table
			 lin-addr ptr-table-base-addr wp smep nxe
			 r-w-x cpl x86)))))
  :hints (("Goal" :do-not '(preprocess)
	   :in-theory (e/d (rm-low-64-and-page-dir-ptr-table-1G-pages
			    ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p)
			   (not
			    member-p-cons
			    disjoint-p-cons
			    unsigned-byte-p
			    signed-byte-p)))))

(defrule re-read-entry-still-valid-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)
		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))
	   (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
	    lin-addr ptr-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
	    (mv-nth
	     2
	     (ia32e-la-to-pa-page-dir-ptr-table
	      lin-addr ptr-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
  :do-not '(preprocess)
  :in-theory (e/d (page-dir-ptr-table-components-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-dir-ptr-table-1G-pages)
		  (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1g-pages
		   not
		   unsigned-byte-p
		   signed-byte-p)))

;; 2M pages:

(defrule relating-validity-of-two-entries-in-two-x86-states-wrt-page-dir-ptr-table-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr
		 ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal entry-1 (rm-low-64 ptr-table-entry-addr x86))
		(equal entry-2 (rm-low-64 ptr-table-entry-addr x86-another))

		(equal (ia32e-page-tables-slice :ps entry-1) 0)

		(ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
		 '4K-or-2M entry-1 entry-2)

		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd entry-1)
			    12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry-1 (rm-low-64 page-directory-entry-addr x86))
		(equal page-directory-entry-2 (rm-low-64 page-directory-entry-addr x86-another))

		(equal (ia32e-page-tables-slice :ps page-directory-entry-1) 1)

		(ia32e-la-to-pa-page-directory-entry-components-equal-p
		 '2M page-directory-entry-1 page-directory-entry-2))

	   (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
	    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86-another))
  :in-theory (e/d
	      (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p)
	      ()))

(defruled page-dir-ptr-table-components-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-dir-ptr-table-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry)
			    12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)

		;; (disjoint-p (addr-range 8 ptr-table-entry-addr)
		;;          (addr-range 8 page-directory-entry-addr))

		(pairwise-disjoint-p
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))
		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))
	   (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
	    '4K-or-2M
	    (rm-low-64 ptr-table-entry-addr x86)
	    (rm-low-64 ptr-table-entry-addr
		       (mv-nth
			2
			(ia32e-la-to-pa-page-dir-ptr-table
			 lin-addr ptr-table-base-addr wp smep nxe
			 r-w-x cpl x86)))))
  :hints (("Goal" :do-not '(preprocess)
	   :in-theory (e/d
		       (rm-low-64-and-page-dir-ptr-table-2M-pages
			ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p)
		       (mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
			mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2m-pages
			mv-nth-1-no-error-ia32e-la-to-pa-page-directory-2m-pages
			ia32e-la-to-pa-page-dir-ptr-table-entry-validp
			not
			member-p-cons
			disjoint-p-cons
			unsigned-byte-p
			signed-byte-p)))))

(defruled page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-page-dir-ptr-table-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry)
			    12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)

		;; (disjoint-p (addr-range 8 ptr-table-entry-addr)
		;;          (addr-range 8 page-directory-entry-addr))
		(pairwise-disjoint-p
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))

		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))

	   (ia32e-la-to-pa-page-directory-entry-components-equal-p
	    '2M
	    (rm-low-64 page-directory-entry-addr x86)
	    (rm-low-64
	     page-directory-entry-addr
	     (mv-nth
	      2
	      (ia32e-la-to-pa-page-dir-ptr-table
	       lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)))))
  :hints (("Goal" :do-not '(preprocess)
	   :in-theory (e/d
		       (page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-page-directory-2M-pages)
		       (not
			mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2m-pages
			mv-nth-1-no-error-ia32e-la-to-pa-page-directory-2m-pages
			member-p-cons
			ia32e-la-to-pa-page-directory-entry-validp
			disjoint-p-cons
			unsigned-byte-p
			signed-byte-p)))))

(defrule re-read-entry-still-valid-ia32e-la-to-pa-page-dir-ptr-table-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)
		;; (disjoint-p
		;;  (addr-range 8 ptr-table-entry-addr)
		;;  (addr-range 8 page-directory-entry-addr))
		(pairwise-disjoint-p
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))
		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))

	   (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
	    lin-addr ptr-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
	    (mv-nth
	     2
	     (ia32e-la-to-pa-page-dir-ptr-table
	      lin-addr ptr-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
  :do-not '(preprocess)
  :in-theory (e/d
	      (page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-page-dir-ptr-table-2M-pages
	       page-dir-ptr-table-components-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-dir-ptr-table-2M-pages)
	      (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
	       mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
	       mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2m-pages
	       not
	       unsigned-byte-p
	       signed-byte-p)))

;; 4K pages:

(defrule relating-validity-of-two-entries-in-two-x86-states-wrt-page-dir-ptr-table-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal entry-1 (rm-low-64 ptr-table-entry-addr x86))
		(equal entry-2 (rm-low-64 ptr-table-entry-addr x86-another))
		(equal (ia32e-page-tables-slice :ps entry-1) 0)
		(ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
		 '4K-or-2M entry-1 entry-2)

		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd entry-1)
			    12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry-1 (rm-low-64 page-directory-entry-addr x86))
		(equal page-directory-entry-2 (rm-low-64 page-directory-entry-addr x86-another))

		(equal (ia32e-page-tables-slice :ps page-directory-entry-1) 0)

		(ia32e-la-to-pa-page-directory-entry-components-equal-p
		 '4K page-directory-entry-1 page-directory-entry-2)

		(equal page-table-base-addr-1
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry-1) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr-1))

		(equal table-entry-1 (rm-low-64 page-table-entry-addr x86))
		(equal table-entry-2 (rm-low-64 page-table-entry-addr x86-another))

		(ia32e-la-to-pa-page-table-entry-components-equal-p
		 table-entry-1 table-entry-2))

	   (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
	    lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86-another))
  :in-theory (e/d
	      (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p)
	      ()))

(defruled page-dir-ptr-table-components-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-dir-ptr-table-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))

		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)

		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))

		(pairwise-disjoint-p
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))

		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))
	   (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
	    '4K-or-2M
	    (rm-low-64 ptr-table-entry-addr x86)
	    (rm-low-64 ptr-table-entry-addr
		       (mv-nth
			2
			(ia32e-la-to-pa-page-dir-ptr-table
			 lin-addr ptr-table-base-addr wp smep nxe
			 r-w-x cpl x86)))))
  :hints (("Goal" :do-not '(preprocess)
	   :in-theory (e/d
		       (rm-low-64-and-page-dir-ptr-table-4K-pages
			ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p)
		       (mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
			mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
			mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
			ia32e-la-to-pa-page-dir-ptr-table-entry-validp
			not
			member-p-cons
			disjoint-p-cons
			unsigned-byte-p
			signed-byte-p)))))

(defruled page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-page-dir-ptr-table-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))

		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)

		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))

		(pairwise-disjoint-p
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))

		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))
	   (ia32e-la-to-pa-page-directory-entry-components-equal-p
	    '4K
	    (rm-low-64 page-directory-entry-addr x86)
	    (rm-low-64 page-directory-entry-addr
		       (mv-nth
			2
			(ia32e-la-to-pa-page-dir-ptr-table
			 lin-addr ptr-table-base-addr wp smep nxe
			 r-w-x cpl x86)))))
  :hints (("Goal" :do-not '(preprocess)
	   :in-theory (e/d
		       (page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-page-directory-4K-pages)
		       (not
			mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
			mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
			member-p-cons
			ia32e-la-to-pa-page-directory-entry-validp
			disjoint-p-cons
			unsigned-byte-p
			signed-byte-p)))))

(defruled page-table-components-equal-rm-low-64-of-page-table-entry-addr-via-page-dir-ptr-table-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))

		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)

		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))

		(pairwise-disjoint-p
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))
		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))

	   (ia32e-la-to-pa-page-table-entry-components-equal-p
	    (rm-low-64 page-table-entry-addr x86)
	    (rm-low-64
	     page-table-entry-addr
	     (mv-nth
	      2
	      (ia32e-la-to-pa-page-dir-ptr-table
	       lin-addr ptr-table-base-addr wp smep nxe
	       r-w-x cpl x86)))))
  :hints (("Goal" :do-not '(preprocess)
	   :in-theory (e/d
		       (page-table-components-equal-rm-low-64-of-page-table-entry-addr-via-page-directory-4K-pages)
		       (mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
			mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4k-pages
			not
			member-p-cons
			disjoint-p-cons
			unsigned-byte-p
			signed-byte-p)))))

(defrule re-read-entry-still-valid-ia32e-la-to-pa-page-dir-ptr-table-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))

		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)

		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))

		(pairwise-disjoint-p
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))

		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))

	   (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
	    lin-addr ptr-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
	    (mv-nth
	     2
	     (ia32e-la-to-pa-page-dir-ptr-table
	      lin-addr ptr-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
  :do-not '(preprocess)
  :in-theory (e/d
	      (page-dir-ptr-table-components-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-dir-ptr-table-4K-pages
	       page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-page-dir-ptr-table-4K-pages
	       page-table-components-equal-rm-low-64-of-page-table-entry-addr-via-page-dir-ptr-table-4K-pages)
	      (mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
	       mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
	       ia32e-la-to-pa-page-dir-ptr-table-entry-validp
	       mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
	       not
	       unsigned-byte-p
	       signed-byte-p)))

;; ......................................................................
;; Two page directory pointer table walks theorem --- same addresses:
;; ......................................................................

;; 1G pages:

(defrule two-page-table-walks-ia32e-la-to-pa-dir-ptr-table-1G-pages-same-addresses

  ;; Key lemmas needed:

  ;; 1. mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1g-pages
  ;; 2. reading-entry-with-accessed-and-dirty-bits-set-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
  ;; 3. reading-entry-with-accessed-bit-set-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
  ;; 4. reading-entry-with-dirty-bit-set-ia32e-la-to-pa-page-dir-ptr-table-1G-pages

  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)
		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))
	   (equal
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-dir-ptr-table
	      lin-addr ptr-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
	      (mv-nth
	       2
	       (ia32e-la-to-pa-page-dir-ptr-table
		lin-addr ptr-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-dir-ptr-table
	      lin-addr ptr-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86))))
  :do-not '(preprocess)
  :in-theory (e/d
	      ()
	      (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
	       mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
	       mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
	       mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
	       mv-nth-1-no-error-ia32e-la-to-pa-page-directory-2M-pages
	       mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
	       mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
	       member-p-cons
	       disjoint-p-cons
	       not
	       unsigned-byte-p
	       signed-byte-p)))

(defrule two-page-table-walks-ia32e-la-to-pa-dir-ptr-table-1G-pages-same-entry-different-addrs
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr-1 ptr-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr-2 ptr-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
		(equal ptr-table-entry-addr-1
		       (page-dir-ptr-table-entry-addr lin-addr-1 ptr-table-base-addr))
		(equal ptr-table-entry-1 (rm-low-64 ptr-table-entry-addr-1 x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry-1) 1)
		;; So that the ptr table entries are the same...
		(equal (part-select lin-addr-1 :low 30 :high 38)
		       (part-select lin-addr-2 :low 30 :high 38))
		;; So that the physical addresses are different...
		(not (equal (part-select lin-addr-1 :low 0 :high 29)
			    (part-select lin-addr-2 :low 0 :high 29)))
		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr-1)
		(canonical-address-p lin-addr-2)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))
	   (equal
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-dir-ptr-table
	      lin-addr-1 ptr-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
	      (mv-nth
	       2
	       (ia32e-la-to-pa-page-dir-ptr-table
		lin-addr-2 ptr-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-dir-ptr-table
	      lin-addr-1 ptr-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86))))
  :do-not '(preprocess)
  :use ((:instance equality-of-page-dir-ptr-table-entry-addr))
  :in-theory (e/d
	      ()
	      (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
	       mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
	       mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
	       mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
	       mv-nth-1-no-error-ia32e-la-to-pa-page-directory-2M-pages
	       mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
	       mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
	       member-p-cons
	       disjoint-p-cons
	       not
	       unsigned-byte-p
	       signed-byte-p)))

;; 2M pages:

(defruled page-dir-ptr-table-components-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-directory-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry)
			    12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)

		;; (disjoint-p (addr-range 8 ptr-table-entry-addr)
		;;          (addr-range 8 page-directory-entry-addr))
		(pairwise-disjoint-p
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))

		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))
	   (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
	    '4K-or-2M
	    (rm-low-64 ptr-table-entry-addr x86)
	    (rm-low-64 ptr-table-entry-addr
		       (mv-nth
			2
			(ia32e-la-to-pa-page-directory
			 lin-addr page-directory-base-addr
			 wp smep nxe r-w-x cpl x86)))))
  :hints (("Goal" :do-not '(preprocess)
	   :in-theory (e/d
		       (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p)
		       (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
			mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
			mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2m-pages
			mv-nth-1-no-error-ia32e-la-to-pa-page-directory-2m-pages
			ia32e-la-to-pa-page-dir-ptr-table-entry-validp
			not
			member-p-cons
			disjoint-p-cons
			unsigned-byte-p
			signed-byte-p)))))

(defrule re-read-entry-still-page-dir-ptr-table-valid-page-directory-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)
		;; (disjoint-p
		;;  (addr-range 8 ptr-table-entry-addr)
		;;  (addr-range 8 page-directory-entry-addr))
		(pairwise-disjoint-p
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))
		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))

	   (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
	    lin-addr ptr-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
	    (mv-nth
	     2
	     (ia32e-la-to-pa-page-directory
	      lin-addr page-directory-base-addr
	      wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
  :do-not '(preprocess)
  :in-theory (e/d
	      (page-dir-ptr-table-components-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-directory-2M-pages
	       page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-page-directory-2M-pages)
	      (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
	       mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
	       mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2m-pages
	       not
	       unsigned-byte-p
	       signed-byte-p)))

(defruled page-size-from-re-reading-page-directory-entry-given-page-directory-entry-validp-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-directory-entry-validp
		 lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86)
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  page-directory-entry) 1)
		(physical-address-p page-directory-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 page-directory-base-addr) 0)
		(x86p x86))
	   (equal
	    (ia32e-page-tables-slice
	     :ps
	     (rm-low-64 page-directory-entry-addr
			(mv-nth
			 2
			 (ia32e-la-to-pa-page-directory
			  lin-addr page-directory-base-addr wp smep nxe r-w-x
			  cpl x86))))
	    (ia32e-page-tables-slice :ps page-directory-entry)))
  :do-not '(preprocess)
  :in-theory (e/d* (rm-low-64-and-page-directory-2M-pages)
		   (ia32e-la-to-pa-page-directory-entry-validp
		    not
		    unsigned-byte-p
		    signed-byte-p)))

(defrule two-page-table-walks-ia32e-la-to-pa-dir-ptr-table-2M-pages-same-addresses

  ;; Key lemmas:

  ;; mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
  ;; re-read-entry-still-page-dir-ptr-table-valid-page-directory-2m-pages
  ;; reading-entry-with-accessed-bit-set-ia32e-la-to-pa-page-dir-ptr-table-2m-pages
  ;; mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
  ;; page-dir-ptr-entry-validp-to-page-directory-entry-validp
  ;; two-page-table-walks-ia32e-la-to-pa-page-directory-2m-pages

  ;; Note that for this theorem, we also need:
  ;; page-size-from-re-reading-page-directory-entry-given-page-directory-entry-validp-2M-pages

  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))

		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)

		(pairwise-disjoint-p
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))
		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))
	   (equal
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-dir-ptr-table
	      lin-addr ptr-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
	      (mv-nth
	       2
	       (ia32e-la-to-pa-page-dir-ptr-table
		lin-addr ptr-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-dir-ptr-table
	      lin-addr ptr-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86))))
  :do-not '(preprocess)
  :in-theory (e/d
	      (page-size-from-re-reading-page-directory-entry-given-page-directory-entry-validp-2M-pages)
	      (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
	       mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
	       mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
	       mv-nth-1-no-error-ia32e-la-to-pa-page-directory-2M-pages
	       mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
	       mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
	       member-p-cons
	       disjoint-p-cons
	       not
	       unsigned-byte-p
	       signed-byte-p)))

(defruled page-dir-ptr-table-entry-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-directory-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr-1 ptr-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr-2 ptr-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
		(equal ptr-table-entry-addr-1
		       (page-dir-ptr-table-entry-addr lin-addr-1 ptr-table-base-addr))
		(equal ptr-table-entry-1 (rm-low-64 ptr-table-entry-addr-1 x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry-1) 0)

		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry-1) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr-1 page-directory-base-addr))

		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)

		(pairwise-disjoint-p
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr-1 ptr-table-base-addr x86))

		;; So that the ptr table entries are the same...
		(equal (part-select lin-addr-1 :low 30 :high 38)
		       (part-select lin-addr-2 :low 30 :high 38))
		;; So that the page directory entries are the same...
		(equal (part-select lin-addr-1 :low 21 :high 29)
		       (part-select lin-addr-2 :low 21 :high 29))
		;; So that the physical address is different...
		(not (equal (part-select lin-addr-1 :low 0 :high 20)
			    (part-select lin-addr-2 :low 0 :high 20)))

		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr-1)
		(canonical-address-p lin-addr-2)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))
	   (equal
	    (rm-low-64
	     ptr-table-entry-addr-1
	     (mv-nth
	      2
	      (ia32e-la-to-pa-page-directory
	       lin-addr-2 page-directory-base-addr wp-2 smep-2 nxe-2 r-w-x-2
	       cpl-2 x86)))
	    (rm-low-64 ptr-table-entry-addr-1 x86)))
  :hints (("Goal" :do-not '(preprocess)
	   :use ((:instance equality-of-page-dir-ptr-table-entry-addr)
		 (:instance equality-of-page-directory-entry-addr))
	   :in-theory (e/d
		       (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p)
		       (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
			not
			member-p-cons
			disjoint-p-cons
			unsigned-byte-p
			signed-byte-p)))))

(defrule re-read-entry-still-page-dir-ptr-table-valid-page-directory-2M-pages-same-entry-different-addrs
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr-1 ptr-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr-2 ptr-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
		(equal ptr-table-entry-addr-1
		       (page-dir-ptr-table-entry-addr lin-addr-1 ptr-table-base-addr))
		(equal ptr-table-entry-1 (rm-low-64 ptr-table-entry-addr-1 x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry-1) 0)

		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry-1) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr-1 page-directory-base-addr))

		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)

		(pairwise-disjoint-p
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr-1 ptr-table-base-addr x86))

		;; So that the ptr table entries are the same...
		(equal (part-select lin-addr-1 :low 30 :high 38)
		       (part-select lin-addr-2 :low 30 :high 38))
		;; So that the page directory entries are the same...
		(equal (part-select lin-addr-1 :low 21 :high 29)
		       (part-select lin-addr-2 :low 21 :high 29))
		;; So that the physical address is different...
		(not (equal (part-select lin-addr-1 :low 0 :high 20)
			    (part-select lin-addr-2 :low 0 :high 20)))

		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr-1)
		(canonical-address-p lin-addr-2)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))
	   (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
	    lin-addr-1 ptr-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
	    (mv-nth
	     2
	     (ia32e-la-to-pa-page-directory
	      lin-addr-2 page-directory-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
  :hints (("Goal" :do-not '(preprocess)
	   :use ((:instance equality-of-page-dir-ptr-table-entry-addr)
		 (:instance equality-of-page-directory-entry-addr))
	   :in-theory (e/d
		       (ia32e-la-to-pa-page-directory-entry-components-equal-p
			page-dir-ptr-table-entry-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-directory-2M-pages
			page-dir-ptr-table-components-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-directory-2M-pages)
		       (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
			not
			member-p-cons
			disjoint-p-cons
			ia32e-la-to-pa-page-table-entry-validp
			unsigned-byte-p
			signed-byte-p)))))

(defrule two-page-table-walks-ia32e-la-to-pa-dir-ptr-table-2M-pages-same-entry-different-addrs
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr-1 ptr-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr-2 ptr-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
		(equal ptr-table-entry-addr-1
		       (page-dir-ptr-table-entry-addr lin-addr-1 ptr-table-base-addr))
		(equal ptr-table-entry-1 (rm-low-64 ptr-table-entry-addr-1 x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry-1) 0)

		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry-1) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr-1 page-directory-base-addr))

		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)

		(pairwise-disjoint-p
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr-1 ptr-table-base-addr x86))

		;; So that the ptr table entries are the same...
		(equal (part-select lin-addr-1 :low 30 :high 38)
		       (part-select lin-addr-2 :low 30 :high 38))
		;; So that the page directory entries are the same...
		(equal (part-select lin-addr-1 :low 21 :high 29)
		       (part-select lin-addr-2 :low 21 :high 29))
		;; So that the physical address is different...
		(not (equal (part-select lin-addr-1 :low 0 :high 20)
			    (part-select lin-addr-2 :low 0 :high 20)))

		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr-1)
		(canonical-address-p lin-addr-2)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))
	   (equal
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-dir-ptr-table
	      lin-addr-1 ptr-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
	      (mv-nth
	       2
	       (ia32e-la-to-pa-page-dir-ptr-table
		lin-addr-2 ptr-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-dir-ptr-table
	      lin-addr-1 ptr-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86))))
  :do-not '(preprocess)
  :use ((:instance equality-of-page-dir-ptr-table-entry-addr)
	(:instance equality-of-page-directory-entry-addr))
  :in-theory (e/d
	      (page-size-from-re-reading-page-directory-entry-given-page-directory-entry-validp-2M-pages
	       page-size-from-re-reading-page-directory-entry-given-page-directory-entry-validp-2M-pages
	       page-dir-ptr-table-entry-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-directory-2M-pages)
	      (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
	       mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
	       mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
	       mv-nth-1-no-error-ia32e-la-to-pa-page-directory-2M-pages
	       mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
	       mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
	       member-p-cons
	       disjoint-p-cons
	       not
	       unsigned-byte-p
	       signed-byte-p)))

;; 4K pages:

(defruled page-dir-ptr-table-components-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-directory-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))

		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)

		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))


		(pairwise-disjoint-p
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))
		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))
	   (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
	    '4K-or-2M
	    (rm-low-64 ptr-table-entry-addr x86)
	    (rm-low-64 ptr-table-entry-addr
		       (mv-nth
			2
			(ia32e-la-to-pa-page-directory
			 lin-addr page-directory-base-addr
			 wp smep nxe r-w-x cpl x86)))))
  :hints (("Goal" :do-not '(preprocess)
	   :in-theory (e/d
		       (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p)
		       (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
			mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
			mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
			mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
			ia32e-la-to-pa-page-dir-ptr-table-entry-validp
			not
			member-p-cons
			disjoint-p-cons
			unsigned-byte-p
			signed-byte-p)))))

(defrule re-read-entry-still-page-dir-ptr-table-valid-page-directory-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))

		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)

		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))

		(pairwise-disjoint-p
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))
		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))
	   (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
	    lin-addr ptr-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
	    (mv-nth
	     2
	     (ia32e-la-to-pa-page-directory
	      lin-addr page-directory-base-addr
	      wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
  :do-not '(preprocess)
  :in-theory (e/d
	      (page-dir-ptr-table-components-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-directory-4K-pages
	       page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-page-directory-4K-pages
	       page-table-components-equal-rm-low-64-of-page-table-entry-addr-via-page-directory-4K-pages)
	      (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
	       mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
	       mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
	       not
	       unsigned-byte-p
	       signed-byte-p)))

(defruled page-size-from-reading-page-dir-ptr-table-entry-from-state-after-page-directory-given-page-dir-ptr-table-entry-validp-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))

		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)

		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))

		(pairwise-disjoint-p
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))
		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))
	   (equal (ia32e-page-tables-slice
		   :ps
		   (rm-low-64
		    ptr-table-entry-addr
		    (mv-nth
		     2
		     (ia32e-la-to-pa-page-directory
		      lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86))))
		  ;; (ia32e-page-tables-slice
		  ;;  :ps
		  ;;  (rm-low-64 ptr-table-entry-addr x86))
		  0
		  ))

  :do-not '(preprocess)
  :in-theory (e/d (rm-low-64-and-page-directory-4K-pages
		   rm-low-64-and-page-dir-ptr-table-4K-pages)
		  (ia32e-la-to-pa-page-directory-entry-validp
		   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   not
		   unsigned-byte-p
		   signed-byte-p)))

(defruled page-size-from-re-reading-page-directory-entry-given-page-dir-ptr-table-entry-validp-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))

		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)

		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))

		(pairwise-disjoint-p
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))
		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))
	   (equal (ia32e-page-tables-slice
		   :ps
		   (rm-low-64
		    page-directory-entry-addr
		    (mv-nth
		     2
		     (ia32e-la-to-pa-page-directory
		      lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86))))
		  ;; (ia32e-page-tables-slice
		  ;;  :ps
		  ;;  (rm-low-64 page-directory-entry-addr x86))
		  0
		  ))

  :do-not '(preprocess)
  :in-theory (e/d (rm-low-64-and-page-directory-4K-pages
		   rm-low-64-and-page-dir-ptr-table-4K-pages)
		  (ia32e-la-to-pa-page-directory-entry-validp
		   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   not
		   unsigned-byte-p
		   signed-byte-p)))

(defruled logtail-12-of-reading-page-directory-entry-from-state-after-page-directory-given-page-dir-ptr-table-validp
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))

		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)

		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))

		(pairwise-disjoint-p
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))
		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))
	   (equal
	    (logtail 12
		     (rm-low-64
		      page-directory-entry-addr
		      (mv-nth
		       2
		       (ia32e-la-to-pa-page-directory
			lin-addr page-directory-base-addr wp smep nxe r-w-x cpl x86))))
	    (logtail 12 (rm-low-64 page-directory-entry-addr x86))))

  :do-not '(preprocess)
  :in-theory (e/d (rm-low-64-and-page-directory-4K-pages
		   rm-low-64-and-page-dir-ptr-table-4K-pages)
		  (ia32e-la-to-pa-page-directory-entry-validp
		   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   not
		   unsigned-byte-p
		   signed-byte-p)))

(defrule two-page-table-walks-ia32e-la-to-pa-dir-ptr-table-4K-pages-same-addresses

  ;; Key lemmas:
  ;; mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
  ;; re-read-entry-still-page-dir-ptr-table-valid-page-directory-4K-pages
  ;; reading-entry-with-accessed-bit-set-ia32e-la-to-pa-page-dir-ptr-table-4K-pages
  ;; mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
  ;; page-dir-ptr-entry-validp-to-page-directory-entry-validp
  ;; two-page-table-walks-ia32e-la-to-pa-page-directory-4K-pages

  ;; Note that for this theorem, we also need:
  ;; page-size-from-reading-page-dir-ptr-table-entry-from-state-after-page-directory-given-page-dir-ptr-table-entry-validp-4K-pages
  ;; page-size-from-re-reading-page-directory-entry-given-page-dir-ptr-table-entry-validp-4K-pages
  ;; logtail-12-of-reading-page-directory-entry-from-state-after-page-directory-given-page-dir-ptr-table-validp

  ;; I discovered that I needed the above lemmas by doing:
  ;; (acl2::why reading-entry-with-accessed-bit-set-ia32e-la-to-pa-page-dir-ptr-table-4k-pages)

  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))

		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)

		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))
		(pairwise-disjoint-p
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))
		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))
	   (equal
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-dir-ptr-table
	      lin-addr ptr-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
	      (mv-nth
	       2
	       (ia32e-la-to-pa-page-dir-ptr-table
		lin-addr ptr-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-dir-ptr-table
	      lin-addr ptr-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86))))
  :do-not '(preprocess)
  :in-theory (e/d
	      (page-size-from-reading-page-dir-ptr-table-entry-from-state-after-page-directory-given-page-dir-ptr-table-entry-validp-4K-pages
	       page-size-from-re-reading-page-directory-entry-given-page-dir-ptr-table-entry-validp-4K-pages
	       logtail-12-of-reading-page-directory-entry-from-state-after-page-directory-given-page-dir-ptr-table-validp)
	      (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
	       mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
	       mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
	       mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
	       mv-nth-1-no-error-ia32e-la-to-pa-page-directory-2M-pages
	       mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
	       mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
	       member-p-cons
	       disjoint-p-cons
	       not
	       unsigned-byte-p
	       signed-byte-p)))

(defruled page-dir-ptr-table-entry-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-directory-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr-1 ptr-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr-2 ptr-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
		(equal ptr-table-entry-addr-1
		       (page-dir-ptr-table-entry-addr lin-addr-1 ptr-table-base-addr))
		(equal ptr-table-entry-1 (rm-low-64 ptr-table-entry-addr-1 x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry-1) 0)

		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry-1) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr-1 page-directory-base-addr))

		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)

		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr-1 page-table-base-addr))

		(pairwise-disjoint-p
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr-1 ptr-table-base-addr x86))

		;; So that the ptr table entries are the same...
		(equal (part-select lin-addr-1 :low 30 :high 38)
		       (part-select lin-addr-2 :low 30 :high 38))
		;; So that the page directory entries are the same...
		(equal (part-select lin-addr-1 :low 21 :high 29)
		       (part-select lin-addr-2 :low 21 :high 29))
		;; So that the page table entries are the same...
		(equal (part-select lin-addr-1 :low 12 :high 20)
		       (part-select lin-addr-2 :low 12 :high 20))
		;; So that the physical address is different...
		(not (equal (part-select lin-addr-1 :low 0 :width 12)
			    (part-select lin-addr-2 :low 0 :width 12)))

		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr-1)
		(canonical-address-p lin-addr-2)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))
	   (equal
	    (rm-low-64
	     ptr-table-entry-addr-1
	     (mv-nth
	      2
	      (ia32e-la-to-pa-page-directory
	       lin-addr-2 page-directory-base-addr wp-2 smep-2 nxe-2 r-w-x-2
	       cpl-2 x86)))
	    (rm-low-64 ptr-table-entry-addr-1 x86)))
  :hints (("Goal" :do-not '(preprocess)
	   :use ((:instance equality-of-page-dir-ptr-table-entry-addr)
		 (:instance equality-of-page-directory-entry-addr)
		 (:instance equality-of-page-table-entry-addr))
	   :in-theory (e/d
		       (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p)
		       (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
			not
			member-p-cons
			disjoint-p-cons
			unsigned-byte-p
			signed-byte-p)))))

(defrule re-read-entry-still-page-dir-ptr-table-valid-page-directory-4K-pages-same-entry-different-addrs
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr-1 ptr-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr-2 ptr-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
		(equal ptr-table-entry-addr-1
		       (page-dir-ptr-table-entry-addr lin-addr-1 ptr-table-base-addr))
		(equal ptr-table-entry-1 (rm-low-64 ptr-table-entry-addr-1 x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry-1) 0)

		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry-1) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr-1 page-directory-base-addr))

		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)

		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr-1 page-table-base-addr))

		(pairwise-disjoint-p
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr-1 ptr-table-base-addr x86))

		;; So that the ptr table entries are the same...
		(equal (part-select lin-addr-1 :low 30 :high 38)
		       (part-select lin-addr-2 :low 30 :high 38))
		;; So that the page directory entries are the same...
		(equal (part-select lin-addr-1 :low 21 :high 29)
		       (part-select lin-addr-2 :low 21 :high 29))
		;; So that the page table entries are the same...
		(equal (part-select lin-addr-1 :low 12 :high 20)
		       (part-select lin-addr-2 :low 12 :high 20))
		;; So that the physical address is different...
		(not (equal (part-select lin-addr-1 :low 0 :width 12)
			    (part-select lin-addr-2 :low 0 :width 12)))

		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr-1)
		(canonical-address-p lin-addr-2)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))
	   (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
	    lin-addr-1 ptr-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
	    (mv-nth
	     2
	     (ia32e-la-to-pa-page-directory
	      lin-addr-2 page-directory-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
  :hints (("Goal" :do-not '(preprocess)
	   :use ((:instance equality-of-page-dir-ptr-table-entry-addr)
		 (:instance equality-of-page-directory-entry-addr)
		 (:instance equality-of-page-table-entry-addr))
	   :in-theory (e/d
		       (ia32e-la-to-pa-page-directory-entry-components-equal-p
			page-dir-ptr-table-entry-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-directory-2M-pages
			page-dir-ptr-table-components-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-directory-2M-pages)
		       (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
			not
			member-p-cons
			disjoint-p-cons
			ia32e-la-to-pa-page-table-entry-validp
			unsigned-byte-p
			signed-byte-p)))))

(defrule two-page-table-walks-ia32e-la-to-pa-dir-ptr-table-4K-pages-same-entry-different-addrs
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr-1 ptr-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr-2 ptr-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
		(equal ptr-table-entry-addr-1
		       (page-dir-ptr-table-entry-addr lin-addr-1 ptr-table-base-addr))
		(equal ptr-table-entry-1 (rm-low-64 ptr-table-entry-addr-1 x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry-1) 0)

		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry-1) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr-1 page-directory-base-addr))

		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)

		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr-1 page-table-base-addr))

		(pairwise-disjoint-p
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr-1 ptr-table-base-addr x86))

		;; So that the ptr table entries are the same...
		(equal (part-select lin-addr-1 :low 30 :high 38)
		       (part-select lin-addr-2 :low 30 :high 38))
		;; So that the page directory entries are the same...
		(equal (part-select lin-addr-1 :low 21 :high 29)
		       (part-select lin-addr-2 :low 21 :high 29))
		;; So that the page table entries are the same...
		(equal (part-select lin-addr-1 :low 12 :high 20)
		       (part-select lin-addr-2 :low 12 :high 20))
		;; So that the physical address is different...
		(not (equal (part-select lin-addr-1 :low 0 :width 12)
			    (part-select lin-addr-2 :low 0 :width 12)))

		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr-1)
		(canonical-address-p lin-addr-2)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))
	   (equal
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-dir-ptr-table
	      lin-addr-1 ptr-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
	      (mv-nth
	       2
	       (ia32e-la-to-pa-page-dir-ptr-table
		lin-addr-2 ptr-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-dir-ptr-table
	      lin-addr-1 ptr-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86))))
  :do-not '(preprocess)
  :use ((:instance equality-of-page-dir-ptr-table-entry-addr)
	(:instance equality-of-page-directory-entry-addr)
	(:instance equality-of-page-table-entry-addr))
  :in-theory (e/d
	      (page-dir-ptr-table-entry-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-directory-4K-pages
	       page-size-from-reading-page-dir-ptr-table-entry-from-state-after-page-directory-given-page-dir-ptr-table-entry-validp-4K-pages
	       page-size-from-re-reading-page-directory-entry-given-page-dir-ptr-table-entry-validp-4K-pages
	       logtail-12-of-reading-page-directory-entry-from-state-after-page-directory-given-page-dir-ptr-table-validp)
	      (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
	       mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
	       mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
	       mv-nth-1-no-error-ia32e-la-to-pa-page-directory-2M-pages
	       mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
	       mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
	       member-p-cons
	       disjoint-p-cons
	       not
	       unsigned-byte-p
	       signed-byte-p)))

;; ......................................................................
;; Two page directory pointer table walks theorem --- different
;; entries:
;; ......................................................................

(defrule two-page-table-walks-ia32e-la-to-pa-page-dir-ptr-table-different-entries

  ;; Key lemmas:

  ;; mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
  ;; mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
  ;; mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages-with-disjoint-wm-low-64
  ;; mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-2M-pages-with-disjoint-wm-low-64
  ;; mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-pages-with-disjoint-wm-low-64

  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr-1 ptr-table-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr-2 ptr-table-base-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)

		(pairwise-disjoint-p
		 (append
		  (translation-governing-addresses-for-page-dir-ptr-table
		   lin-addr-2 ptr-table-base-addr-2 x86)
		  (translation-governing-addresses-for-page-dir-ptr-table
		   lin-addr-1 ptr-table-base-addr-1 x86)))

		(physical-address-p ptr-table-base-addr-1)
		(canonical-address-p lin-addr-1)
		(equal (loghead 12 ptr-table-base-addr-1) 0)

		(physical-address-p ptr-table-base-addr-2)
		(canonical-address-p lin-addr-2)
		(equal (loghead 12 ptr-table-base-addr-2) 0)

		(x86p x86))
	   (equal
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-dir-ptr-table
	      lin-addr-1 ptr-table-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
	      (mv-nth
	       2
	       (ia32e-la-to-pa-page-dir-ptr-table
		lin-addr-2 ptr-table-base-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
	    (mv-nth
	     1
	     (ia32e-la-to-pa-page-dir-ptr-table
	      lin-addr-1 ptr-table-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
	      x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-page-directory-entry-components-equal-p)
		  (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		   ;; mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
		   ;; mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
		   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-2M-pages
		   mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   member-p-cons
		   disjoint-p-cons
		   not
		   unsigned-byte-p
		   signed-byte-p)))

;; ......................................................................
;; More theorems about validity of page directory pointer table
;; entries being preserved when the translation-governing addresses
;; are disjoint:
;; ......................................................................

(defrule validity-preserved-same-x86-state-disjoint-addresses-wrt-page-dir-ptr-table
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr-1 ptr-table-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr-2 ptr-table-base-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)

		(pairwise-disjoint-p
		 (append
		  (translation-governing-addresses-for-page-dir-ptr-table
		   lin-addr-2 ptr-table-base-addr-2 x86)
		  (translation-governing-addresses-for-page-dir-ptr-table
		   lin-addr-1 ptr-table-base-addr-1 x86)))

		(physical-address-p ptr-table-base-addr-1)
		(canonical-address-p lin-addr-1)
		(equal (loghead 12 ptr-table-base-addr-1) 0)

		(physical-address-p ptr-table-base-addr-2)
		(canonical-address-p lin-addr-2)
		(equal (loghead 12 ptr-table-base-addr-2) 0)

		(x86p x86))

	   (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
	    lin-addr-1 ptr-table-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
	    (mv-nth 2 (ia32e-la-to-pa-page-dir-ptr-table
		       lin-addr-2 ptr-table-base-addr-2
		       wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))

  :in-theory (e/d ()
		  (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2M-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
		   member-p-cons
		   disjoint-p-cons
		   not
		   unsigned-byte-p
		   signed-byte-p)))

;; ......................................................................
;; Translation-Governing-Addresses-For-Page-Dir-Ptr-Table and
;; ia32e-la-to-pa-page-dir-ptr-table-entry:
;; ......................................................................

(defrule translation-governing-addresses-for-page-dir-ptr-table-and-ia32e-la-to-pa-page-dir-ptr-table-pairwise-disjoint
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr-2 ptr-table-base-addr-2 wp-2
		 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
		(pairwise-disjoint-p
		 (append
		  (translation-governing-addresses-for-page-dir-ptr-table
		   lin-addr-2 ptr-table-base-addr-2 x86)
		  (translation-governing-addresses-for-page-dir-ptr-table
		   lin-addr-1 ptr-table-base-addr-1 x86)))
		(physical-address-p ptr-table-base-addr-2))
	   (equal
	    (translation-governing-addresses-for-page-dir-ptr-table
	     lin-addr-1 ptr-table-base-addr-1
	     (mv-nth 2
		     (ia32e-la-to-pa-page-dir-ptr-table
		      lin-addr-2 ptr-table-base-addr-2
		      wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)))
	    (translation-governing-addresses-for-page-dir-ptr-table
	     lin-addr-1 ptr-table-base-addr-1 x86)))
  :in-theory (e/d ()
		  (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		   addr-range-1
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
		   member-p-cons
		   disjoint-p-cons
		   not
		   unsigned-byte-p
		   signed-byte-p)))

;; 1G pages:

(defrule translation-governing-addresses-for-page-dir-ptr-table-and-ia32e-la-to-pa-page-dir-ptr-table-same-addr-1G-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp
		 smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal page-dir-ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-dir-ptr-table-entry) 1)

		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))
	   (equal
	    (translation-governing-addresses-for-page-dir-ptr-table
	     lin-addr ptr-table-base-addr
	     (mv-nth 2
		     (ia32e-la-to-pa-page-dir-ptr-table
		      lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)))
	    (translation-governing-addresses-for-page-dir-ptr-table
	     lin-addr ptr-table-base-addr x86)))
  :in-theory (e/d ()
		  (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		   translation-governing-addresses-for-page-directory
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
		   addr-range-1
		   member-p-cons
		   disjoint-p-cons
		   not
		   unsigned-byte-p
		   signed-byte-p)))

(defrule translation-governing-addresses-for-page-dir-ptr-table-and-disjoint-wm-low-64-1G-pages
  :parents (reasoning-about-page-tables)
  (implies (and (bind-free '((wp . wp)
			     (smep . smep)
			     (nxe . nxe)
			     (r-w-x . r-w-x)
			     (cpl . cpl))
			   (wp smep nxe r-w-x cpl))
		(ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal page-dir-ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-dir-ptr-table-entry) 1)

		(pairwise-disjoint-p-aux
		 (addr-range 8 addr)
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))
		(integerp addr))
	   (equal
	    (translation-governing-addresses-for-page-dir-ptr-table
	     lin-addr ptr-table-base-addr (wm-low-64 addr val x86))
	    (translation-governing-addresses-for-page-dir-ptr-table
	     lin-addr ptr-table-base-addr x86)))
  :in-theory (e/d ()
		  (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		   translation-governing-addresses-for-page-directory
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
		   addr-range-1
		   member-p-cons
		   disjoint-p-cons
		   not
		   unsigned-byte-p
		   signed-byte-p)))

;; 2M pages:

(defrule translation-governing-addresses-for-page-dir-ptr-table-and-ia32e-la-to-pa-page-dir-ptr-table-same-addr-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal page-dir-ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-dir-ptr-table-entry) 0)
		;; For page directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd page-dir-ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))

		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)

		;; (disjoint-p
		;;  (addr-range 8 ptr-table-base-addr)
		;;  (addr-range 8 page-directory-entry-addr))
		(pairwise-disjoint-p
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))


		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))
	   (equal
	    (translation-governing-addresses-for-page-dir-ptr-table
	     lin-addr ptr-table-base-addr
	     (mv-nth 2
		     (ia32e-la-to-pa-page-dir-ptr-table
		      lin-addr ptr-table-base-addr
		      wp smep nxe r-w-x cpl x86)))
	    (translation-governing-addresses-for-page-dir-ptr-table
	     lin-addr ptr-table-base-addr x86)))
  :in-theory (e/d* ()
		   (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		    mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
		    addr-range-1
		    member-p-cons
		    disjoint-p-cons
		    not
		    unsigned-byte-p
		    signed-byte-p)))

(defrule translation-governing-addresses-for-page-dir-ptr-table-and-disjoint-wm-low-64-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (bind-free '((wp . wp)
			     (smep . smep)
			     (nxe . nxe)
			     (r-w-x . r-w-x)
			     (cpl . cpl))
			   (wp smep nxe r-w-x cpl))
		(ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal page-dir-ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-dir-ptr-table-entry) 0)
		;; For page directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd page-dir-ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))

		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)
		(pairwise-disjoint-p
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))
		(pairwise-disjoint-p-aux
		 (addr-range 8 addr)
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))
		(integerp addr)
		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))
	   (equal
	    (translation-governing-addresses-for-page-dir-ptr-table
	     lin-addr ptr-table-base-addr
	     (wm-low-64 addr val x86))
	    (translation-governing-addresses-for-page-dir-ptr-table
	     lin-addr ptr-table-base-addr x86)))
  :in-theory (e/d ()
		  (translation-governing-addresses-for-page-directory
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
		   addr-range-1
		   member-p-cons
		   disjoint-p-cons
		   not
		   unsigned-byte-p
		   signed-byte-p)))

;; 4K pages:

(defrule translation-governing-addresses-for-page-dir-ptr-table-and-ia32e-la-to-pa-page-dir-ptr-table-same-addr-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal page-dir-ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-dir-ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd page-dir-ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))

		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)

		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))
		(pairwise-disjoint-p
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))

		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))
	   (equal
	    (translation-governing-addresses-for-page-dir-ptr-table
	     lin-addr ptr-table-base-addr
	     (mv-nth 2
		     (ia32e-la-to-pa-page-dir-ptr-table
		      lin-addr ptr-table-base-addr
		      wp smep nxe r-w-x cpl x86)))
	    (translation-governing-addresses-for-page-dir-ptr-table
	     lin-addr ptr-table-base-addr x86)))
  :in-theory (e/d* (
		    )
		   (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		    mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
		    addr-range-1
		    member-p-cons
		    disjoint-p-cons
		    not
		    unsigned-byte-p
		    signed-byte-p)))

(defrule translation-governing-addresses-for-page-dir-ptr-table-and-disjoint-wm-low-64-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (bind-free '((wp . wp)
			     (smep . smep)
			     (nxe . nxe)
			     (r-w-x . r-w-x)
			     (cpl . cpl))
			   (wp smep nxe r-w-x cpl))
		(ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		 lin-addr ptr-table-base-addr wp smep nxe r-w-x cpl x86)
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal page-dir-ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-dir-ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd page-dir-ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))

		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)

		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))
		(pairwise-disjoint-p
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))
		(pairwise-disjoint-p-aux
		 (addr-range 8 addr)
		 (translation-governing-addresses-for-page-dir-ptr-table
		  lin-addr ptr-table-base-addr x86))

		(integerp addr)
		(physical-address-p ptr-table-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 ptr-table-base-addr) 0)
		(x86p x86))
	   (equal
	    (translation-governing-addresses-for-page-dir-ptr-table
	     lin-addr ptr-table-base-addr
	     (wm-low-64 addr val x86))
	    (translation-governing-addresses-for-page-dir-ptr-table
	     lin-addr ptr-table-base-addr x86)))
  :in-theory (e/d ()
		  (translation-governing-addresses-for-page-directory
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
		   addr-range-1
		   member-p-cons
		   disjoint-p-cons
		   not
		   unsigned-byte-p
		   signed-byte-p)))

(in-theory (e/d () (ia32e-la-to-pa-page-dir-ptr-table-entry-validp)))

;; ======================================================================

;; ia32e-la-to-pa-pml4-table:

(defmacro ia32e-la-to-pa-pml4-table-entry-components-equal-p-body
  (entry-1 entry-2)
  `(and (equal (ia32e-pml4e-slice :pml4e-p ,entry-1)
	       (ia32e-pml4e-slice :pml4e-p ,entry-2))
	(equal (ia32e-pml4e-slice :pml4e-r/w ,entry-1)
	       (ia32e-pml4e-slice :pml4e-r/w ,entry-2))
	(equal (ia32e-pml4e-slice :pml4e-u/s ,entry-1)
	       (ia32e-pml4e-slice :pml4e-u/s ,entry-2))
	(equal (ia32e-pml4e-slice :pml4e-ps ,entry-1)
	       (ia32e-pml4e-slice :pml4e-ps ,entry-2))
	(equal (ia32e-pml4e-slice :pml4e-pdpt ,entry-1)
	       (ia32e-pml4e-slice :pml4e-pdpt ,entry-2))
	(equal (ia32e-pml4e-slice :pml4e-xd ,entry-1)
	       (ia32e-pml4e-slice :pml4e-xd ,entry-2))
	;; Reserved bits are zero.
	;; (equal (loghead 11 (logtail 52 ,entry-2)) 0)
	;; (equal (loghead 17 (logtail 13 ,entry-2)) 0)
	(equal (loghead 11 (logtail 52 ,entry-1))
	       (loghead 11 (logtail 52 ,entry-2)))
	(equal (loghead  4 (logtail  8 ,entry-1))
	       (loghead  4 (logtail  8 ,entry-2)))))

(define ia32e-la-to-pa-pml4-table-entry-components-equal-p
  (entry-1 entry-2)
  :verify-guards nil
  :non-executable t
  (ia32e-la-to-pa-pml4-table-entry-components-equal-p-body
   entry-1 entry-2))

(defmacro ia32e-la-to-pa-pml4-table-entry-components-equal-p-macro (x y)
  `(ia32e-la-to-pa-pml4-table-entry-components-equal-p-body
    ,x ,y))

(defthm ia32e-la-to-pa-pml4-table-entry-components-equal-p-reflexive
  (ia32e-la-to-pa-pml4-table-entry-components-equal-p b b)
  :hints (("Goal" :in-theory (e/d
			      (ia32e-la-to-pa-pml4-table-entry-components-equal-p)
			      ()))))

(defthm ia32e-la-to-pa-pml4-table-entry-components-equal-p-accessed-bit-set
  (ia32e-la-to-pa-pml4-table-entry-components-equal-p
   b (logior 32 (logand 18446744073709551583 b)))
  :hints (("Goal" :in-theory (e/d
			      (ia32e-la-to-pa-pml4-table-entry-components-equal-p)
			      ()))))

;; ......................................................................
;; Establishing inferior data structure entry validity from pml4 table
;; entry's validity:
;; ......................................................................

(defrule pml4-table-entry-validp-to-page-dir-ptr-entry-validp
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12)))
	   (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
	    lin-addr ptr-table-base-addr
	    wp smep nxe r-w-x cpl x86)))

(defrule pml4-table-entry-validp-to-page-directory-entry-validp
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12)))
	   (ia32e-la-to-pa-page-directory-entry-validp
	    lin-addr page-directory-base-addr
	    wp smep nxe r-w-x cpl x86)))

(defrule pml4-table-entry-validp-to-page-table-entry-validp
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
		;; For ia32e-la-to-pa-page-table:
		(equal page-table-pml4-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal u-s-acc (ia32e-page-tables-slice :u/s
							page-directory-entry)))
	   (ia32e-la-to-pa-page-table-entry-validp
	    lin-addr page-table-pml4-base-addr u-s-acc wp smep nxe r-w-x cpl x86)))

;; ......................................................................
;; Rules about the three return values of
;; ia32e-la-to-pa-pml4-table:
;; ......................................................................

(defrule mv-nth-0-no-error-ia32e-la-to-pa-pml4-table
  :parents (reasoning-about-page-tables)
  (implies (ia32e-la-to-pa-pml4-table-entry-validp
	    lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
	   (equal (mv-nth
		   0
		   (ia32e-la-to-pa-pml4-table
		    lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86))
		  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table)
		  (not)))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-pml4-table
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal entry (rm-low-64 pml4-entry-addr x86)))
	   (equal (mv-nth
		   1
		   (ia32e-la-to-pa-pml4-table
		    lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86))
		  (mv-nth
		   1
		   (ia32e-la-to-pa-page-dir-ptr-table
		    lin-addr
		    (ash (ia32e-pml4e-slice :pml4e-pdpt entry) 12)
		    wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table)
		  (not
		   mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
		   mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1g-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages)))

(defrule mv-nth-2-no-error-ia32e-la-to-pa-pml4-table
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal entry (rm-low-64 pml4-entry-addr x86))
		(equal accessed (ia32e-page-tables-slice :a entry))
		(equal accessed-entry
		       (if (equal accessed 0)
			   (!ia32e-page-tables-slice :a 1 entry)
			 entry)))
	   (equal (mv-nth
		   2
		   (ia32e-la-to-pa-pml4-table
		    lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86))
		  (let* ((ptpr-x86
			  (mv-nth
			   2
			   (ia32e-la-to-pa-page-dir-ptr-table
			    lin-addr
			    (ash (ia32e-pml4e-slice :pml4e-pdpt entry) 12)
			    wp smep nxe r-w-x cpl x86)))
			 (accessed-x86
			  (if (equal accessed 0)
			      (wm-low-64 pml4-entry-addr accessed-entry ptpr-x86)
			    ptpr-x86)))
		    accessed-x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table)
		  (not
		   mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
		   mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages)))


;; 1G pages:

(defrule mv-nth-0-no-error-ia32e-la-to-pa-pml4-table-1G-pages-with-disjoint-!memi
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

		(pairwise-disjoint-p-aux
		 (addr-range 1 addr)
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))
		(integerp addr))
	   (equal (mv-nth
		   0
		   (ia32e-la-to-pa-pml4-table
		    lin-addr pml4-base-addr wp smep nxe r-w-x cpl
		    (xw :mem addr val x86)))
		  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table)
		  (not
		   addr-range-1
		   unsigned-byte-p
		   signed-byte-p)))

(defrule mv-nth-0-no-error-ia32e-la-to-pa-pml4-table-1G-pages-with-disjoint-wm-low-64
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

		(pairwise-disjoint-p-aux
		 (addr-range 8 addr)
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))
		(integerp addr))
	   (equal (mv-nth
		   0
		   (ia32e-la-to-pa-pml4-table
		    lin-addr pml4-base-addr wp smep nxe r-w-x cpl
		    (wm-low-64 addr val x86)))
		  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table)
		  (not
		   unsigned-byte-p
		   signed-byte-p)))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-pml4-table-1G-pages-with-disjoint-!memi
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

		(pairwise-disjoint-p-aux
		 (addr-range 1 addr)
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86)))
	   (equal (mv-nth
		   1
		   (ia32e-la-to-pa-pml4-table
		    lin-addr pml4-base-addr wp smep nxe r-w-x cpl
		    (xw :mem addr val x86)))
		  (mv-nth
		   1
		   (ia32e-la-to-pa-pml4-table
		    lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table)
		  (not
		   addr-range-1
		   unsigned-byte-p
		   signed-byte-p)))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-pml4-table-1G-pages-with-disjoint-wm-low-64
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

		(pairwise-disjoint-p-aux
		 (addr-range 8 addr)
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))
		(integerp addr))
	   (equal (mv-nth
		   1
		   (ia32e-la-to-pa-pml4-table
		    lin-addr pml4-base-addr wp smep nxe r-w-x cpl
		    (wm-low-64 addr val x86)))
		  (mv-nth
		   1
		   (ia32e-la-to-pa-pml4-table
		    lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table)
		  (not
		   unsigned-byte-p
		   signed-byte-p)))

;; 2M pages:

(defrule mv-nth-0-no-error-ia32e-la-to-pa-pml4-table-2M-pages-with-disjoint-!memi
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)

		(pairwise-disjoint-p-aux
		 (addr-range 1 addr)
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))
		(integerp addr))
	   (equal (mv-nth
		   0
		   (ia32e-la-to-pa-pml4-table
		    lin-addr pml4-base-addr wp smep nxe r-w-x cpl
		    (xw :mem addr val x86)))
		  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table)
		  (not
		   addr-range-1
		   unsigned-byte-p
		   signed-byte-p)))

(defrule mv-nth-0-no-error-ia32e-la-to-pa-pml4-table-2M-pages-with-disjoint-wm-low-64
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)

		(pairwise-disjoint-p-aux
		 (addr-range 8 addr)
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))
		(integerp addr))
	   (equal (mv-nth
		   0
		   (ia32e-la-to-pa-pml4-table
		    lin-addr pml4-base-addr wp smep nxe r-w-x cpl
		    (wm-low-64 addr val x86)))
		  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table)
		  (not
		   unsigned-byte-p
		   signed-byte-p)))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-pml4-table-2M-pages-with-disjoint-!memi
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)

		(pairwise-disjoint-p-aux
		 (addr-range 1 addr)
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))
		(integerp addr))
	   (equal (mv-nth
		   1
		   (ia32e-la-to-pa-pml4-table
		    lin-addr pml4-base-addr wp smep nxe r-w-x cpl
		    (xw :mem addr val x86)))
		  (mv-nth
		   1
		   (ia32e-la-to-pa-pml4-table
		    lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table)
		  (mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
		   not
		   addr-range-1
		   unsigned-byte-p
		   signed-byte-p)))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-pml4-table-2M-pages-with-disjoint-wm-low-64
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)

		(pairwise-disjoint-p-aux
		 (addr-range 8 addr)
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))
		(integerp addr))
	   (equal (mv-nth
		   1
		   (ia32e-la-to-pa-pml4-table
		    lin-addr pml4-base-addr wp smep nxe r-w-x cpl
		    (wm-low-64 addr val x86)))
		  (mv-nth
		   1
		   (ia32e-la-to-pa-pml4-table
		    lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table)
		  (not
		   mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
		   unsigned-byte-p
		   signed-byte-p)))

;; 4K pages:

(defrule mv-nth-0-no-error-ia32e-la-to-pa-pml4-table-4K-pages-with-disjoint-!memi
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))

		(pairwise-disjoint-p-aux
		 (addr-range 1 addr)
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))
		(integerp addr))
	   (equal (mv-nth
		   0
		   (ia32e-la-to-pa-pml4-table
		    lin-addr pml4-base-addr wp smep nxe r-w-x cpl
		    (xw :mem addr val x86)))
		  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table)
		  (not
		   addr-range-1
		   unsigned-byte-p
		   signed-byte-p)))

(defrule mv-nth-0-no-error-ia32e-la-to-pa-pml4-table-4K-pages-with-disjoint-wm-low-64
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))

		(pairwise-disjoint-p-aux
		 (addr-range 8 addr)
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))
		(integerp addr))
	   (equal (mv-nth
		   0
		   (ia32e-la-to-pa-pml4-table
		    lin-addr pml4-base-addr wp smep nxe r-w-x cpl
		    (wm-low-64 addr val x86)))
		  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table)
		  (not
		   unsigned-byte-p
		   signed-byte-p)))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-pml4-table-4K-pages-with-disjoint-!memi
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))

		(pairwise-disjoint-p-aux
		 (addr-range 1 addr)
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))
		(integerp addr))
	   (equal (mv-nth
		   1
		   (ia32e-la-to-pa-pml4-table
		    lin-addr pml4-base-addr wp smep nxe r-w-x cpl
		    (xw :mem addr val x86)))
		  (mv-nth
		   1
		   (ia32e-la-to-pa-pml4-table
		    lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table)
		  (not
		   mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
		   addr-range-1
		   unsigned-byte-p
		   signed-byte-p)))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-pml4-table-4K-pages-with-disjoint-wm-low-64
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))

		(pairwise-disjoint-p-aux
		 (addr-range 8 addr)
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))
		(integerp addr))
	   (equal (mv-nth
		   1
		   (ia32e-la-to-pa-pml4-table
		    lin-addr pml4-base-addr wp smep nxe r-w-x cpl
		    (wm-low-64 addr val x86)))
		  (mv-nth
		   1
		   (ia32e-la-to-pa-pml4-table
		    lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table)
		  (not
		   mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
		   unsigned-byte-p
		   signed-byte-p)))

;; ......................................................................
;; Reading pml4-table-entry-addr again using rm-low-64:
;; ......................................................................

;; 1G pages:

(defruled rm-low-64-and-ia32e-la-to-pa-pml4-table-1G-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

		(pairwise-disjoint-p
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))

		(physical-address-p pml4-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 pml4-base-addr) 0)
		(x86p x86))
	   (equal
	    (rm-low-64 pml4-entry-addr
		       (mv-nth
			2
			(ia32e-la-to-pa-pml4-table
			 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)))
	    (cond
	     ((equal (ia32e-page-tables-slice :a pml4-entry) 1)
	      ;; Accessed bit is set.
	      (rm-low-64 pml4-entry-addr x86))

	     (t ;; Accessed is clear.
	      (!ia32e-page-tables-slice
	       :a 1
	       (rm-low-64 pml4-entry-addr x86))))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table)
		  (not
		   mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
		   mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
		   unsigned-byte-p
		   signed-byte-p)))

;; 2M pages:

(defruled rm-low-64-and-ia32e-la-to-pa-pml4-table-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)

		(pairwise-disjoint-p
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))

		(physical-address-p pml4-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 pml4-base-addr) 0)
		(x86p x86))
	   (equal
	    (rm-low-64 pml4-entry-addr
		       (mv-nth
			2
			(ia32e-la-to-pa-pml4-table
			 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)))
	    (cond
	     ((equal (ia32e-page-tables-slice :a pml4-entry) 1)
	      ;; Accessed bit is set.
	      (rm-low-64 pml4-entry-addr x86))

	     (t ;; Accessed is clear.
	      (!ia32e-page-tables-slice
	       :a 1
	       (rm-low-64 pml4-entry-addr x86))))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table)
		  (not
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
		   unsigned-byte-p
		   signed-byte-p)))

;; 4K pages:

(defruled rm-low-64-and-ia32e-la-to-pa-pml4-table-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))


		(pairwise-disjoint-p
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))


		(physical-address-p pml4-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 pml4-base-addr) 0)
		(x86p x86))
	   (equal
	    (rm-low-64 pml4-entry-addr
		       (mv-nth
			2
			(ia32e-la-to-pa-pml4-table
			 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)))
	    (cond
	     ((equal (ia32e-page-tables-slice :a pml4-entry) 1)
	      ;; Accessed bit is set.
	      (rm-low-64 pml4-entry-addr x86))

	     (t ;; Accessed is clear.
	      (!ia32e-page-tables-slice
	       :a 1
	       (rm-low-64 pml4-entry-addr x86))))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table)
		  (not
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
		   unsigned-byte-p
		   signed-byte-p)))

;; ......................................................................
;; !memi and state after data structure walk WoW theorem:
;; ......................................................................

;; 1G pages:

(defrule disjoint-!memi-mv-nth-2-no-error-ia32e-la-to-pa-pml4-table-1G-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

		(pairwise-disjoint-p-aux
		 (addr-range 1 addr)
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))
		(integerp addr))
	   (equal
	    (mv-nth
	     2
	     (ia32e-la-to-pa-pml4-table
	      lin-addr pml4-base-addr wp smep nxe r-w-x cpl
	      (xw :mem addr val x86)))
	    (xw :mem addr val
		   (mv-nth
		    2
		    (ia32e-la-to-pa-pml4-table
		     lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table
		   wm-low-64 wm-low-32)
		  (not
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages)))

;; 2M pages:

(defrule disjoint-!memi-mv-nth-2-no-error-ia32e-la-to-pa-pml4-table-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)

		(pairwise-disjoint-p-aux
		 (addr-range 1 addr)
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))
		(integerp addr))
	   (equal
	    (mv-nth
	     2
	     (ia32e-la-to-pa-pml4-table
	      lin-addr pml4-base-addr wp smep nxe r-w-x cpl
	      (xw :mem addr val x86)))
	    (xw :mem addr val
		   (mv-nth
		    2
		    (ia32e-la-to-pa-pml4-table
		     lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table
		   wm-low-64 wm-low-32)
		  (not
		   addr-range-1
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages)))

;; 4K pages:

(defrule disjoint-!memi-mv-nth-2-no-error-ia32e-la-to-pa-pml4-table-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))

		(pairwise-disjoint-p-aux
		 (addr-range 1 addr)
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))

		(integerp addr))
	   (equal
	    (mv-nth
	     2
	     (ia32e-la-to-pa-pml4-table
	      lin-addr pml4-base-addr wp smep nxe r-w-x cpl
	      (xw :mem addr val x86)))
	    (xw :mem
	     addr val
	     (mv-nth
	      2
	      (ia32e-la-to-pa-pml4-table
	       lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table
		   wm-low-64 wm-low-32
		   )
		  (not
		   addr-range-1
		   acl2::mv-nth-cons-meta
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4k-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages)))

;; ......................................................................
;; Reading addresses disjoint from pml4-table-entry-addr after
;; walking the pml4 table:
;; ......................................................................

;; 1G pages:

(defrule disjoint-memi-read-mv-nth-2-no-error-ia32e-la-to-pa-pml4-table-1G-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

		(pairwise-disjoint-p-aux
		 (addr-range 1 addr)
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86)))
	   (equal
	    (xr :mem addr
		  (mv-nth
		   2
		   (ia32e-la-to-pa-pml4-table
		    lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)))
	    (xr :mem addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table
		   wm-low-64 wm-low-32)
		  (not
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages)))

(defrule disjoint-rm-low-64-read-mv-nth-2-no-error-ia32e-la-to-pa-pml4-table-1G-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

		(pairwise-disjoint-p-aux
		 (addr-range 8 addr)
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))
		(integerp addr))
	   (equal
	    (rm-low-64 addr
		       (mv-nth
			2
			(ia32e-la-to-pa-pml4-table
			 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)))
	    (rm-low-64 addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table)
		  (not
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages)))

(defrule disjoint-rm-low-32-read-mv-nth-2-no-error-ia32e-la-to-pa-pml4-table-1G-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

		(pairwise-disjoint-p-aux
		 (addr-range 4 addr)
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))

		(integerp addr))
	   (equal
	    (rm-low-32 addr
		       (mv-nth
			2
			(ia32e-la-to-pa-pml4-table
			 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)))
	    (rm-low-32 addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table
		   wm-low-64)
		  (not
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages)))

;; 2M pages:

(defrule disjoint-memi-read-mv-nth-2-no-error-ia32e-la-to-pa-pml4-table-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)

		(pairwise-disjoint-p-aux
		 (addr-range 1 addr)
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86)))
	   (equal
	    (xr :mem addr
		  (mv-nth
		   2
		   (ia32e-la-to-pa-pml4-table
		    lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)))
	    (xr :mem addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table)
		  (not
		   addr-range-1
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages)))

(defrule disjoint-rm-low-64-read-mv-nth-2-no-error-ia32e-la-to-pa-pml4-table-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)

		(pairwise-disjoint-p-aux
		 (addr-range 8 addr)
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))
		(integerp addr))
	   (equal
	    (rm-low-64 addr
		       (mv-nth
			2
			(ia32e-la-to-pa-pml4-table
			 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)))
	    (rm-low-64 addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table)
		  (not
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages)))

(defrule disjoint-rm-low-32-read-mv-nth-2-no-error-ia32e-la-to-pa-pml4-table-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)

		(pairwise-disjoint-p-aux
		 (addr-range 4 addr)
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))
		(integerp addr))
	   (equal
	    (rm-low-32 addr
		       (mv-nth
			2
			(ia32e-la-to-pa-pml4-table
			 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)))
	    (rm-low-32 addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table
		   wm-low-64)
		  (not
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages)))

;; 4K pages:

(defrule disjoint-memi-read-mv-nth-2-no-error-ia32e-la-to-pa-pml4-table-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))

		(pairwise-disjoint-p-aux
		 (addr-range 1 addr)
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86)))
	   (equal
	    (xr :mem
	     addr
	     (mv-nth
	      2
	      (ia32e-la-to-pa-pml4-table
	       lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)))
	    (xr :mem addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table
		   wm-low-64 wm-low-32)
		  (not
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages)))

(defrule disjoint-rm-low-64-read-mv-nth-2-no-error-ia32e-la-to-pa-pml4-table-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))

		(pairwise-disjoint-p-aux
		 (addr-range 8 addr)
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))
		(integerp addr))
	   (equal
	    (rm-low-64
	     addr
	     (mv-nth
	      2
	      (ia32e-la-to-pa-pml4-table
	       lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)))
	    (rm-low-64 addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table)
		  (not
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages)))

(defrule disjoint-rm-low-32-read-mv-nth-2-no-error-ia32e-la-to-pa-pml4-table-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))

		(pairwise-disjoint-p-aux
		 (addr-range 4 addr)
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))
		(integerp addr))
	   (equal
	    (rm-low-32 addr
		       (mv-nth
			2
			(ia32e-la-to-pa-pml4-table
			 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)))
	    (rm-low-32 addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table
		   wm-low-64)
		  (not
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages)))

;; ......................................................................
;; Theorems that state that the validity of the pml4 table entry is
;; preserved when writes are done to disjoint addresses or :a/:d are
;; set:
;; ......................................................................

;; 1G pages:

(defrule entry-with-disjoint-!memi-still-valid-ia32e-la-to-pa-pml4-table-1G-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

		(pairwise-disjoint-p-aux
		 (addr-range 1 addr)
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))
		(integerp addr)

		(physical-address-p pml4-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 pml4-base-addr) 0)
		(x86p x86))
	   (ia32e-la-to-pa-pml4-table-entry-validp
	    lin-addr pml4-base-addr wp smep nxe r-w-x cpl
	    (xw :mem addr val x86)))
  :in-theory (e/d (ia32e-la-to-pa-pml4-table)
		  (mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
		   not
		   addr-range-1
		   unsigned-byte-p
		   signed-byte-p)))

(defrule entry-with-disjoint-wm-low-64-still-valid-ia32e-la-to-pa-pml4-table-1G-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

		(pairwise-disjoint-p-aux
		 (addr-range 8 addr)
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))
		(integerp addr)

		(physical-address-p pml4-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 pml4-base-addr) 0)
		(x86p x86))
	   (ia32e-la-to-pa-pml4-table-entry-validp
	    lin-addr pml4-base-addr wp smep nxe r-w-x cpl
	    (wm-low-64 addr val x86)))
  :in-theory (e/d (ia32e-la-to-pa-pml4-table)
		  (not
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
		   unsigned-byte-p
		   signed-byte-p)))

(defrule entry-with-accessed-bit-set-still-valid-ia32e-la-to-pa-pml4-table-1G-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

		;; (disjoint-p (addr-range 8 pml4-entry-addr)
		;;          (addr-range 8 ptr-table-entry-addr))
		(pairwise-disjoint-p
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))
		(physical-address-p pml4-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 pml4-base-addr) 0)
		(x86p x86))
	   (ia32e-la-to-pa-pml4-table-entry-validp
	    lin-addr pml4-base-addr wp smep nxe r-w-x cpl
	    (wm-low-64
	     pml4-entry-addr
	     ;; (!ia32e-page-tables-slice :a 1 entry)
	     (logior 32 (logand 18446744073709551583 pml4-entry))
	     x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa-pml4-table)
		  (not
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
		   unsigned-byte-p
		   signed-byte-p)))

;; 2M pages:

(defrule entry-with-disjoint-!memi-still-valid-ia32e-la-to-pa-pml4-table-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)

		(pairwise-disjoint-p-aux
		 (addr-range 1 addr)
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))
		(integerp addr)
		(physical-address-p pml4-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 pml4-base-addr) 0)
		(x86p x86))
	   (ia32e-la-to-pa-pml4-table-entry-validp
	    lin-addr pml4-base-addr wp smep nxe r-w-x cpl
	    (xw :mem addr val x86)))
  :in-theory (e/d ()
		  (mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
		   not
		   addr-range-1
		   unsigned-byte-p
		   signed-byte-p)))

(defrule entry-with-disjoint-wm-low-64-still-valid-ia32e-la-to-pa-pml4-table-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)

		(pairwise-disjoint-p-aux
		 (addr-range 8 addr)
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))
		(integerp addr)
		(physical-address-p pml4-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 pml4-base-addr) 0)
		(x86p x86))
	   (ia32e-la-to-pa-pml4-table-entry-validp
	    lin-addr pml4-base-addr wp smep nxe r-w-x cpl
	    (wm-low-64 addr val x86)))
  :in-theory (e/d (ia32e-la-to-pa-pml4-table
		   rm-low-64-and-ia32e-la-to-pa-pml4-table-2M-pages)
		  (mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
		   not
		   unsigned-byte-p
		   signed-byte-p)))

(defrule entry-with-accessed-bit-set-still-valid-ia32e-la-to-pa-pml4-table-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)

		(pairwise-disjoint-p
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))

		(physical-address-p pml4-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 pml4-base-addr) 0)
		(x86p x86))
	   (ia32e-la-to-pa-pml4-table-entry-validp
	    lin-addr pml4-base-addr wp smep nxe r-w-x cpl
	    (wm-low-64
	     pml4-entry-addr
	     ;; (!ia32e-page-tables-slice :a 1 entry)
	     (logior 32 (logand 18446744073709551583 pml4-entry))
	     x86)))
  :do-not '(preprocess)
  :in-theory (e/d ()
		  (mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
		   not
		   unsigned-byte-p
		   signed-byte-p)))

;; 4K pages:

(defrule entry-with-disjoint-!memi-still-valid-ia32e-la-to-pa-pml4-table-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))

		(pairwise-disjoint-p-aux
		 (addr-range 1 addr)
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))
		(integerp addr)
		(physical-address-p pml4-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 pml4-base-addr) 0)
		(x86p x86))
	   (ia32e-la-to-pa-pml4-table-entry-validp
	    lin-addr pml4-base-addr wp smep nxe r-w-x cpl
	    (xw :mem addr val x86)))
  :in-theory (e/d ()
		  (mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-pml4-table
		   not
		   addr-range-1
		   unsigned-byte-p
		   signed-byte-p)))

(defrule entry-with-disjoint-wm-low-64-still-valid-ia32e-la-to-pa-pml4-table-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))

		(pairwise-disjoint-p-aux
		 (addr-range 8 addr)
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))
		(integerp addr)
		(physical-address-p pml4-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 pml4-base-addr) 0)
		(x86p x86))
	   (ia32e-la-to-pa-pml4-table-entry-validp
	    lin-addr pml4-base-addr wp smep nxe r-w-x cpl
	    (wm-low-64 addr val x86)))
  :in-theory (e/d ()
		  (mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
		   rm-low-64-and-ia32e-la-to-pa-pml4-table-4K-pages
		   not
		   unsigned-byte-p
		   signed-byte-p)))

(defrule entry-with-accessed-bit-set-still-valid-ia32e-la-to-pa-pml4-table-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))


		(pairwise-disjoint-p
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))

		(physical-address-p pml4-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 pml4-base-addr) 0)
		(x86p x86))
	   (ia32e-la-to-pa-pml4-table-entry-validp
	    lin-addr pml4-base-addr wp smep nxe r-w-x cpl
	    (wm-low-64
	     pml4-entry-addr
	     ;; (!ia32e-page-tables-slice :a 1 entry)
	     (logior 32 (logand 18446744073709551583 pml4-entry))
	     x86)))
  :do-not '(preprocess)
  :in-theory (e/d ()
		  (rm-low-64-and-ia32e-la-to-pa-pml4-table-4K-pages
		   not
		   unsigned-byte-p
		   signed-byte-p)))

;; ......................................................................
;; Reading pml4 table entry from x86 states where :a/:d are set:
;; ......................................................................

;; 1G pages:

(defrule reading-entry-with-accessed-bit-set-ia32e-la-to-pa-pml4-table-1G-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

		;; (disjoint-p (addr-range 8 pml4-entry-addr)
		;;          (addr-range 8 ptr-table-entry-addr))
		(pairwise-disjoint-p
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))
		(physical-address-p pml4-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 pml4-base-addr) 0)
		(x86p x86))
	   (equal
	    (mv-nth
	     1
	     (ia32e-la-to-pa-pml4-table
	      lin-addr pml4-base-addr wp smep nxe r-w-x cpl
	      (wm-low-64
	       pml4-entry-addr
	       ;; (!ia32e-page-tables-slice :a 1 entry)
	       (logior 32 (logand 18446744073709551583 pml4-entry))
	       x86)))
	    (mv-nth
	     1
	     (ia32e-la-to-pa-pml4-table
	      lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d ()
		  (mv-nth-2-no-error-ia32e-la-to-pa-pml4-table
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
		   not
		   unsigned-byte-p
		   signed-byte-p)))

;; 2M pages:

(defrule reading-entry-with-accessed-bit-set-ia32e-la-to-pa-pml4-table-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)

		(pairwise-disjoint-p
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))

		(physical-address-p pml4-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 pml4-base-addr) 0)
		(x86p x86))
	   (equal
	    (mv-nth
	     1
	     (ia32e-la-to-pa-pml4-table
	      lin-addr pml4-base-addr wp smep nxe r-w-x cpl
	      (wm-low-64
	       pml4-entry-addr
	       ;; (!ia32e-page-tables-slice :a 1 entry)
	       (logior 32 (logand 18446744073709551583 pml4-entry))
	       x86)))
	    (mv-nth
	     1
	     (ia32e-la-to-pa-pml4-table
	      lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d ()
		  (not
		   ia32e-la-to-pa-pml4-table-entry-validp
		   mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-pml4-table
		   unsigned-byte-p
		   signed-byte-p)))

;; 4K pages:

(defrule reading-entry-with-accessed-bit-set-ia32e-la-to-pa-pml4-table-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))

		(pairwise-disjoint-p
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))

		(physical-address-p pml4-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 pml4-base-addr) 0)
		(x86p x86))
	   (equal
	    (mv-nth
	     1
	     (ia32e-la-to-pa-pml4-table
	      lin-addr pml4-base-addr wp smep nxe r-w-x cpl
	      (wm-low-64
	       pml4-entry-addr
	       ;; (!ia32e-page-tables-slice :a 1 entry)
	       (logior 32 (logand 18446744073709551583 pml4-entry))
	       x86)))
	    (mv-nth
	     1
	     (ia32e-la-to-pa-pml4-table
	      lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d ()
		  (not
		   ia32e-la-to-pa-pml4-table-entry-validp
		   mv-nth-2-no-error-ia32e-la-to-pa-pml4-table
		   mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
		   unsigned-byte-p
		   signed-byte-p)))

;; ......................................................................
;; More theorems about preservation of validity of pml4 table entries:
;; ......................................................................

;; 1G pages:

(defrule relating-validity-of-two-entries-in-two-x86-states-wrt-pml4-table-1G-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal entry-1 (rm-low-64 pml4-entry-addr x86))
		(equal entry-2 (rm-low-64 pml4-entry-addr x86-another))
		(ia32e-la-to-pa-pml4-table-entry-components-equal-p
		 entry-1 entry-2)
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt entry-1) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry-1 (rm-low-64 ptr-table-entry-addr x86))
		(equal ptr-table-entry-2 (rm-low-64 ptr-table-entry-addr x86-another))

		(equal (ia32e-page-tables-slice :ps ptr-table-entry-1) 1)
		(ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
		 '1G ptr-table-entry-1 ptr-table-entry-2))

	   (ia32e-la-to-pa-pml4-table-entry-validp
	    lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86-another))
  :in-theory (e/d
	      (ia32e-la-to-pa-pml4-table-entry-components-equal-p
	       ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
	       ia32e-la-to-pa-pml4-table-entry-validp)
	      ()))

(defruled pml4-table-components-equal-rm-low-64-of-pml4-entry-addr-via-pml4-table-1G-pages
  :parents (reasoning-about-page-tables)

  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

		;; (disjoint-p (addr-range 8 pml4-entry-addr)
		;;          (addr-range 8 ptr-table-entry-addr))
		(pairwise-disjoint-p
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))
		(physical-address-p pml4-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 pml4-base-addr) 0)
		(x86p x86))
	   (ia32e-la-to-pa-pml4-table-entry-components-equal-p
	    (rm-low-64 pml4-entry-addr x86)
	    (rm-low-64
	     pml4-entry-addr
	     (mv-nth
	      2
	      (ia32e-la-to-pa-pml4-table
	       lin-addr pml4-base-addr
	       wp smep nxe r-w-x cpl x86)))))
  :hints (("Goal" :do-not '(preprocess)
	   :in-theory (e/d (ia32e-la-to-pa-pml4-table-entry-components-equal-p
			    ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p)
			   (mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
			    mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
			    not
			    member-p-cons
			    ia32e-la-to-pa-page-directory-entry-validp
			    disjoint-p-cons
			    unsigned-byte-p
			    signed-byte-p)))))

(defruled page-dir-ptr-table-components-equal-rm-low-64-of-ptr-table-base-addr-via-pml4-table-1G-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

		;; (disjoint-p (addr-range 8 pml4-entry-addr)
		;;          (addr-range 8 ptr-table-entry-addr))
		(pairwise-disjoint-p
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))
		(physical-address-p pml4-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 pml4-base-addr) 0)
		(x86p x86))
	   (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
	    '1G
	    (rm-low-64 ptr-table-entry-addr x86)
	    (rm-low-64
	     ptr-table-entry-addr
	     (mv-nth
	      2
	      (ia32e-la-to-pa-pml4-table
	       lin-addr pml4-base-addr
	       wp smep nxe r-w-x cpl x86)))))
  :hints (("Goal" :do-not '(preprocess)
	   :in-theory (e/d (page-dir-ptr-table-components-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-dir-ptr-table-1G-pages)
			   (mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
			    mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
			    not
			    member-p-cons
			    ia32e-la-to-pa-page-directory-entry-validp
			    disjoint-p-cons
			    unsigned-byte-p
			    signed-byte-p)))))

(defrule re-read-entry-still-valid-ia32e-la-to-pa-pml4-table-1G-pages

  ;; 1. (mv-nth 2 (ia32e-la-to-pa-pml4-table ..)) --> (mv-nth 2
  ;;    (ia32e-la-to-pa-page-dir-ptr-table ...))
  ;;
  ;;    Let's ignore the accessed bit for now.

  ;; 2. relating-validity-of-two-entries-in-two-x86-states-wrt-pml4-table-1G-pages needs
  ;;    the following:
  ;;    ia32e-la-to-pa-pml4-table-entry-components-equal-p
  ;;    ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p

  ;;    x86-another is what we get in (1), i.e., (mv-nth 2
  ;;    (ia32e-la-to-pa-page-dir-ptr-table ...)) (with the :a bit, which
  ;;    we're ignoring for now).

  ;; 3. entry-with-accessed-bit-set-still-valid-ia32e-la-to-pa-pml4-table-1g-pages
  ;;    takes care of the accessed bit case.


  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

		;; (disjoint-p (addr-range 8 pml4-entry-addr)
		;;          (addr-range 8 ptr-table-entry-addr))
		(pairwise-disjoint-p
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))
		(physical-address-p pml4-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 pml4-base-addr) 0)
		(x86p x86))
	   (ia32e-la-to-pa-pml4-table-entry-validp
	    lin-addr pml4-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
	    (mv-nth
	     2
	     (ia32e-la-to-pa-pml4-table
	      lin-addr pml4-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
  :do-not '(preprocess)
  :in-theory (e/d
	      (page-dir-ptr-table-components-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-dir-ptr-table-1G-pages
	       pml4-table-components-equal-rm-low-64-of-pml4-entry-addr-via-pml4-table-1G-pages)
	      (ia32e-la-to-pa-pml4-table-entry-validp
	       not
	       mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-1g-pages
	       mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1g-pages
	       acl2::mv-nth-cons-meta
	       unsigned-byte-p
	       signed-byte-p)))

;; 2M pages:

(defrule relating-validity-of-two-entries-in-two-x86-states-wrt-pml4-table-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal entry-1 (rm-low-64 pml4-entry-addr x86))
		(equal entry-2 (rm-low-64 pml4-entry-addr x86-another))
		(ia32e-la-to-pa-pml4-table-entry-components-equal-p
		 entry-1 entry-2)

		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt entry-1) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry-1 (rm-low-64 ptr-table-entry-addr x86))
		(equal ptr-table-entry-2 (rm-low-64 ptr-table-entry-addr x86-another))
		(equal (ia32e-page-tables-slice :ps ptr-table-entry-1) 0)

		(ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
		 '4K-or-2M ptr-table-entry-1 ptr-table-entry-2)

		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry-1) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry-1 (rm-low-64 page-directory-entry-addr x86))
		(equal page-directory-entry-2 (rm-low-64 page-directory-entry-addr x86-another))

		(equal (ia32e-page-tables-slice :ps page-directory-entry-1) 1)

		(ia32e-la-to-pa-page-directory-entry-components-equal-p
		 '2M page-directory-entry-1 page-directory-entry-2))

	   (ia32e-la-to-pa-pml4-table-entry-validp
	    lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86-another))
  :in-theory (e/d
	      (ia32e-la-to-pa-pml4-table-entry-components-equal-p
	       ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
	       ia32e-la-to-pa-page-directory-entry-components-equal-p)
	      ()))

(defruled pml4-table-components-equal-rm-low-64-of-pml4-entry-addr-via-pml4-table-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)

		(pairwise-disjoint-p
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))

		(physical-address-p pml4-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 pml4-base-addr) 0)
		(x86p x86))
	   (ia32e-la-to-pa-pml4-table-entry-components-equal-p
	    (rm-low-64 pml4-entry-addr x86)
	    (rm-low-64
	     pml4-entry-addr
	     (mv-nth
	      2
	      (ia32e-la-to-pa-pml4-table
	       lin-addr pml4-base-addr
	       wp smep nxe r-w-x cpl x86)))))
  :hints (("Goal" :do-not '(preprocess)
	   :in-theory (e/d
		       (ia32e-la-to-pa-pml4-table-entry-components-equal-p
			ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
			ia32e-la-to-pa-page-directory-entry-components-equal-p)
		       (ia32e-la-to-pa-pml4-table-entry-validp
			disjoint-rm-low-64-read-mv-nth-2-no-error-ia32e-la-to-pa-pml4-table-4k-pages
			subset-p-two-addr-ranges
			disjoint-p-two-addr-ranges-thm-3
			disjoint-p-two-addr-ranges-thm-2
			disjoint-p-two-addr-ranges-thm-1
			<-preserved-by-adding-<-*pseudo-page-size-in-bytes*-commuted
			<-preserved-by-adding-<-*pseudo-page-size-in-bytes*
			not
			mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
			mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
			mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
			member-p-cons
			disjoint-p-cons
			unsigned-byte-p
			signed-byte-p)))))

(defruled page-dir-ptr-table-components-equal-rm-low-64-of-ptr-table-entry-addr-via-pml4-table-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)

		(pairwise-disjoint-p
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))

		(physical-address-p pml4-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 pml4-base-addr) 0)
		(x86p x86))
	   (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
	    '4K-or-2M
	    (rm-low-64 ptr-table-entry-addr x86)
	    (rm-low-64
	     ptr-table-entry-addr
	     (mv-nth
	      2
	      (ia32e-la-to-pa-pml4-table
	       lin-addr pml4-base-addr
	       wp smep nxe r-w-x cpl x86)))))
  :hints (("Goal" :do-not '(preprocess)
	   :in-theory (e/d
		       (page-dir-ptr-table-components-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-dir-ptr-table-2M-pages)
		       (mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
			mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
			disjoint-rm-low-64-read-mv-nth-2-no-error-ia32e-la-to-pa-pml4-table-4k-pages
			not
			member-p-cons
			disjoint-p-cons
			unsigned-byte-p
			signed-byte-p)))))

(defruled page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-pml4-table-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)

		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)

		(pairwise-disjoint-p
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))

		(physical-address-p pml4-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 pml4-base-addr) 0)
		(x86p x86))
	   (ia32e-la-to-pa-page-directory-entry-components-equal-p
	    '2M
	    (rm-low-64 page-directory-entry-addr x86)
	    (rm-low-64
	     page-directory-entry-addr
	     (mv-nth
	      2
	      (ia32e-la-to-pa-pml4-table
	       lin-addr pml4-base-addr
	       wp smep nxe r-w-x cpl x86)))))
  :hints (("Goal" :do-not '(preprocess)
	   :in-theory (e/d
		       (page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-page-dir-ptr-table-2M-pages)
		       (not
			mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
			disjoint-rm-low-64-read-mv-nth-2-no-error-ia32e-la-to-pa-pml4-table-4k-pages
			mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
			member-p-cons
			disjoint-p-cons
			unsigned-byte-p
			signed-byte-p)))))

(defrule re-read-entry-still-valid-ia32e-la-to-pa-pml4-table-2M-pages

  ;;    relating-validity-of-two-entries-in-two-x86-states-wrt-pml4-table-2M-pages needs
  ;;    the following:
  ;;    ia32e-la-to-pa-pml4-table-entry-components-equal-p
  ;;    ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
  ;;    ia32e-la-to-pa-page-directory-entry-components-equal-p

  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)

		(pairwise-disjoint-p
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))

		(physical-address-p pml4-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 pml4-base-addr) 0)
		(x86p x86))

	   (ia32e-la-to-pa-pml4-table-entry-validp
	    lin-addr pml4-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
	    (mv-nth
	     2
	     (ia32e-la-to-pa-pml4-table
	      lin-addr pml4-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
  :do-not '(preprocess)
  :in-theory (e/d
	      (page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-pml4-table-2M-pages
	       page-dir-ptr-table-components-equal-rm-low-64-of-ptr-table-entry-addr-via-pml4-table-2M-pages
	       pml4-table-components-equal-rm-low-64-of-pml4-entry-addr-via-pml4-table-2M-pages)
	      (ia32e-la-to-pa-pml4-table-entry-validp
	       mv-nth-2-no-error-ia32e-la-to-pa-pml4-table
	       not
	       mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
	       mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
	       acl2::mv-nth-cons-meta
	       unsigned-byte-p
	       signed-byte-p)))

;; 4K pages:

(defrule relating-validity-of-two-entries-in-two-x86-states-wrt-pml4-table-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal entry-1 (rm-low-64 pml4-entry-addr x86))
		(equal entry-2 (rm-low-64 pml4-entry-addr x86-another))
		(ia32e-la-to-pa-pml4-table-entry-components-equal-p
		 entry-1 entry-2)

		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt entry-1) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry-1 (rm-low-64 ptr-table-entry-addr x86))
		(equal ptr-table-entry-2 (rm-low-64 ptr-table-entry-addr x86-another))
		(equal (ia32e-page-tables-slice :ps ptr-table-entry-1) 0)

		(ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
		 '4K-or-2M ptr-table-entry-1 ptr-table-entry-2)

		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry-1) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry-1 (rm-low-64 page-directory-entry-addr x86))
		(equal page-directory-entry-2 (rm-low-64 page-directory-entry-addr x86-another))

		(equal (ia32e-page-tables-slice :ps page-directory-entry-1) 0)

		(ia32e-la-to-pa-page-directory-entry-components-equal-p
		 '4K page-directory-entry-1 page-directory-entry-2)

		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry-1) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))
		(equal table-entry-1 (rm-low-64 page-table-entry-addr x86))
		(equal table-entry-2 (rm-low-64 page-table-entry-addr x86-another))

		(ia32e-la-to-pa-page-table-entry-components-equal-p
		 table-entry-1 table-entry-2))

	   (ia32e-la-to-pa-pml4-table-entry-validp
	    lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86-another))
  :in-theory (e/d
	      (ia32e-la-to-pa-pml4-table-entry-components-equal-p
	       ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
	       ia32e-la-to-pa-page-directory-entry-components-equal-p
	       ia32e-la-to-pa-page-table-entry-components-equal-p)
	      ()))

(defruled pml4-table-components-equal-rm-low-64-of-pml4-entry-addr-via-pml4-table-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))

		(pairwise-disjoint-p
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))

		(physical-address-p pml4-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 pml4-base-addr) 0)
		(x86p x86))
	   (ia32e-la-to-pa-pml4-table-entry-components-equal-p
	    (rm-low-64 pml4-entry-addr x86)
	    (rm-low-64
	     pml4-entry-addr
	     (mv-nth
	      2
	      (ia32e-la-to-pa-pml4-table lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)))))
  :hints (("Goal" :do-not '(preprocess)
	   :use ((:instance rm-low-64-and-ia32e-la-to-pa-pml4-table-4K-pages))
	   :in-theory (e/d
		       (ia32e-la-to-pa-pml4-table-entry-components-equal-p
			ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
			ia32e-la-to-pa-page-directory-entry-components-equal-p)
		       (ia32e-la-to-pa-pml4-table-entry-validp
			mv-nth-2-no-error-ia32e-la-to-pa-pml4-table
			disjoint-rm-low-64-read-mv-nth-2-no-error-ia32e-la-to-pa-pml4-table-4k-pages
			subset-p-two-addr-ranges
			disjoint-p-two-addr-ranges-thm-3
			disjoint-p-two-addr-ranges-thm-2
			disjoint-p-two-addr-ranges-thm-1
			<-preserved-by-adding-<-*pseudo-page-size-in-bytes*-commuted
			<-preserved-by-adding-<-*pseudo-page-size-in-bytes*
			not
			mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
			mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
			mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
			member-p-cons
			disjoint-p-cons
			unsigned-byte-p
			signed-byte-p)))))

(defruled page-dir-ptr-table-components-equal-rm-low-64-of-ptr-table-entry-addr-via-pml4-table-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))

		(pairwise-disjoint-p
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))

		(physical-address-p pml4-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 pml4-base-addr) 0)
		(x86p x86))
	   (ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
	    '4K-or-2M
	    (rm-low-64 ptr-table-entry-addr x86)
	    (rm-low-64
	     ptr-table-entry-addr
	     (mv-nth
	      2
	      (ia32e-la-to-pa-pml4-table
	       lin-addr pml4-base-addr
	       wp smep nxe r-w-x cpl x86)))))
  :hints (("Goal" :do-not '(preprocess)
	   :in-theory (e/d
		       (page-dir-ptr-table-components-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-dir-ptr-table-4K-pages)
		       (mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
			mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
			disjoint-rm-low-64-read-mv-nth-2-no-error-ia32e-la-to-pa-pml4-table-2M-pages
			subset-p-two-addr-ranges
			disjoint-p-two-addr-ranges-thm-3
			disjoint-p-two-addr-ranges-thm-2
			disjoint-p-two-addr-ranges-thm-1
			<-preserved-by-adding-<-*pseudo-page-size-in-bytes*-commuted
			<-preserved-by-adding-<-*pseudo-page-size-in-bytes*
			not
			member-p-cons
			disjoint-p-cons
			unsigned-byte-p
			signed-byte-p)))))

(defruled page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-pml4-table-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))

		(pairwise-disjoint-p
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))

		(physical-address-p pml4-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 pml4-base-addr) 0)
		(x86p x86))
	   (ia32e-la-to-pa-page-directory-entry-components-equal-p
	    '4K
	    (rm-low-64 page-directory-entry-addr x86)
	    (rm-low-64
	     page-directory-entry-addr
	     (mv-nth
	      2
	      (ia32e-la-to-pa-pml4-table
	       lin-addr pml4-base-addr
	       wp smep nxe r-w-x cpl x86)))))
  :hints (("Goal" :do-not '(preprocess)
	   :in-theory (e/d
		       (page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-page-dir-ptr-table-4K-pages)
		       (not
			disjoint-rm-low-64-read-mv-nth-2-no-error-ia32e-la-to-pa-pml4-table-2M-pages
			subset-p-two-addr-ranges
			disjoint-p-two-addr-ranges-thm-3
			disjoint-p-two-addr-ranges-thm-2
			disjoint-p-two-addr-ranges-thm-1
			<-preserved-by-adding-<-*pseudo-page-size-in-bytes*-commuted
			<-preserved-by-adding-<-*pseudo-page-size-in-bytes*
			mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
			mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
			member-p-cons
			disjoint-p-cons
			unsigned-byte-p
			signed-byte-p)))))

(defruled page-table-components-equal-rm-low-64-of-page-table-entry-addr-via-pml4-table-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))

		(pairwise-disjoint-p
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))

		(physical-address-p pml4-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 pml4-base-addr) 0)
		(x86p x86))
	   (ia32e-la-to-pa-page-table-entry-components-equal-p
	    (rm-low-64 page-table-entry-addr x86)
	    (rm-low-64
	     page-table-entry-addr
	     (mv-nth
	      2
	      (ia32e-la-to-pa-pml4-table
	       lin-addr pml4-base-addr
	       wp smep nxe r-w-x cpl x86)))))
  :hints (("Goal" :do-not '(preprocess)
	   :in-theory (e/d
		       (page-table-components-equal-rm-low-64-of-page-table-entry-addr-via-page-dir-ptr-table-4K-pages)
		       (mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
			mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
			disjoint-rm-low-64-read-mv-nth-2-no-error-ia32e-la-to-pa-pml4-table-2M-pages
			subset-p-two-addr-ranges
			disjoint-p-two-addr-ranges-thm-3
			disjoint-p-two-addr-ranges-thm-2
			disjoint-p-two-addr-ranges-thm-1
			<-preserved-by-adding-<-*pseudo-page-size-in-bytes*-commuted
			<-preserved-by-adding-<-*pseudo-page-size-in-bytes*
			not
			member-p-cons
			disjoint-p-cons
			unsigned-byte-p
			signed-byte-p)))))

(defrule re-read-entry-still-valid-ia32e-la-to-pa-pml4-table-4K-pages

  ;;    relating-validity-of-two-entries-in-two-x86-states-wrt-pml4-table-4K-pages needs
  ;;    the following:
  ;;    ia32e-la-to-pa-pml4-table-entry-components-equal-p
  ;;    ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p
  ;;    ia32e-la-to-pa-page-directory-entry-components-equal-p
  ;;    ia32e-la-to-pa-page-table-entry-components-equal-p

  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))

		(pairwise-disjoint-p
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))

		(physical-address-p pml4-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 pml4-base-addr) 0)
		(x86p x86))

	   (ia32e-la-to-pa-pml4-table-entry-validp
	    lin-addr pml4-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
	    (mv-nth
	     2
	     (ia32e-la-to-pa-pml4-table
	      lin-addr pml4-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
  :do-not '(preprocess)
  :in-theory (e/d
	      (pml4-table-components-equal-rm-low-64-of-pml4-entry-addr-via-pml4-table-4K-pages
	       page-dir-ptr-table-components-equal-rm-low-64-of-ptr-table-entry-addr-via-pml4-table-4K-pages
	       page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-pml4-table-4K-pages
	       page-table-components-equal-rm-low-64-of-page-table-entry-addr-via-pml4-table-4K-pages)
	      (ia32e-la-to-pa-pml4-table-entry-validp
	       not
	       mv-nth-2-no-error-ia32e-la-to-pa-pml4-table
	       mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
	       mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
	       acl2::mv-nth-cons-meta
	       unsigned-byte-p
	       signed-byte-p)))

;; ......................................................................
;; Two pml4 table walks theorem --- same addresses:
;; ......................................................................

;; 1G pages:

(defruled page-size-from-re-reading-page-dir-ptr-table-entry-given-pml4-entry-validp-1G-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

		;; (disjoint-p (addr-range 8 pml4-entry-addr)
		;;          (addr-range 8 ptr-table-entry-addr))
		(pairwise-disjoint-p
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))
		(physical-address-p pml4-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 pml4-base-addr) 0)
		(x86p x86))
	   (equal (ia32e-page-tables-slice
		   :ps
		   (rm-low-64
		    ptr-table-entry-addr
		    (mv-nth 2
			    (ia32e-la-to-pa-page-dir-ptr-table
			     lin-addr ptr-table-base-addr wp smep
			     nxe r-w-x cpl x86))))
		  1))
  :do-not '(preprocess)
  :in-theory (e/d* (
		    rm-low-64-and-page-dir-ptr-table-1G-pages)
		   (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		    not
		    unsigned-byte-p
		    signed-byte-p)))

(defruled logtail-12-of-reading-page-dir-ptr-table-entry-from-state-after-page-dir-ptr-table-given-pml4-table-validp-1G-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

		;; (disjoint-p (addr-range 8 pml4-entry-addr)
		;;          (addr-range 8 ptr-table-entry-addr))
		(pairwise-disjoint-p
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))
		(physical-address-p pml4-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 pml4-base-addr) 0)
		(x86p x86))
	   (equal (logtail 12
			   (rm-low-64
			    ptr-table-entry-addr
			    (mv-nth 2
				    (ia32e-la-to-pa-page-dir-ptr-table
				     lin-addr ptr-table-base-addr wp smep
				     nxe r-w-x cpl x86))))
		  (logtail 12 (rm-low-64 ptr-table-entry-addr x86))))
  :do-not '(preprocess)
  :in-theory (e/d* (
		    rm-low-64-and-page-dir-ptr-table-1G-pages)
		   (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		    not
		    unsigned-byte-p
		    signed-byte-p)))

(defruled re-read-entry-still-pml4-table-valid-page-dir-ptr-table-1G-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

		;; (disjoint-p (addr-range 8 pml4-entry-addr)
		;;          (addr-range 8 ptr-table-entry-addr))
		(pairwise-disjoint-p
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))
		(physical-address-p pml4-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 pml4-base-addr) 0)
		(x86p x86))
	   (ia32e-la-to-pa-pml4-table-entry-validp
	    lin-addr pml4-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
	    (mv-nth
	     2
	     (ia32e-la-to-pa-page-dir-ptr-table
	      lin-addr ptr-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
  :do-not '(preprocess)
  :in-theory (e/d
	      (page-dir-ptr-table-components-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-dir-ptr-table-1G-pages)
	      (ia32e-la-to-pa-pml4-table-entry-validp
	       not
	       mv-nth-2-no-error-ia32e-la-to-pa-pml4-table
	       mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-1g-pages
	       mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1g-pages
	       acl2::mv-nth-cons-meta
	       unsigned-byte-p
	       signed-byte-p)))

(defrule two-page-table-walks-ia32e-la-to-pa-pml4-table-1G-pages-same-addresses

  ;; Key lemmas needed:
  ;; mv-nth-2-no-error-ia32e-la-to-pa-pml4-table
  ;; re-read-entry-still-pml4-table-valid-page-dir-ptr-table-1G-pages
  ;; reading-entry-with-accessed-bit-set-ia32e-la-to-pa-pml4-table-1G-pages
  ;; mv-nth-1-no-error-ia32e-la-to-pa-pml4-table
  ;; pml4-table-entry-validp-to-page-dir-ptr-entry-validp
  ;; two-page-table-walks-ia32e-la-to-pa-dir-ptr-table-1G-pages-same-addresses

  ;; Note that for this theorem, we also need:
  ;; page-size-from-re-reading-page-dir-ptr-table-entry-given-pml4-entry-validp-1G-pages
  ;; logtail-12-of-reading-page-dir-ptr-table-entry-from-state-after-page-dir-ptr-table-given-pml4-table-validp-1G-pages

  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

		;; (disjoint-p (addr-range 8 pml4-entry-addr)
		;;          (addr-range 8 ptr-table-entry-addr))
		(pairwise-disjoint-p
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))
		(physical-address-p pml4-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 pml4-base-addr) 0)
		(x86p x86))
	   (equal
	    (mv-nth
	     1
	     (ia32e-la-to-pa-pml4-table
	      lin-addr pml4-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
	      (mv-nth
	       2
	       (ia32e-la-to-pa-pml4-table
		lin-addr pml4-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
	    (mv-nth
	     1
	     (ia32e-la-to-pa-pml4-table
	      lin-addr pml4-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86))))
  :do-not '(preprocess)
  :in-theory (e/d (page-size-from-re-reading-page-dir-ptr-table-entry-given-pml4-entry-validp-1G-pages
		   logtail-12-of-reading-page-dir-ptr-table-entry-from-state-after-page-dir-ptr-table-given-pml4-table-validp-1G-pages
		   re-read-entry-still-pml4-table-valid-page-dir-ptr-table-1G-pages)
		  (ia32e-la-to-pa-pml4-table-entry-validp
		   mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-1g-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1g-pages
		   member-p-cons
		   disjoint-p-cons
		   not
		   unsigned-byte-p
		   signed-byte-p)))

(defrule re-read-entry-still-pml4-table-valid-page-dir-ptr-table-1G-pages-same-entry-different-addrs
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr-1 pml4-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr-2 pml4-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr-1 pml4-table-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr-1 ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

		;; So that pml4 table entries are the same...
		(equal (part-select lin-addr-1 :low 39 :high 47)
		       (part-select lin-addr-2 :low 39 :high 47))
		;; So that the ptr table entries are the same...
		(equal (part-select lin-addr-1 :low 30 :high 38)
		       (part-select lin-addr-2 :low 30 :high 38))
		;; So that the physical addresses are different...
		(not (equal (part-select lin-addr-1 :low 0 :high 29)
			    (part-select lin-addr-2 :low 0 :high 29)))

		(pairwise-disjoint-p
		 (translation-governing-addresses-for-pml4-table
		  lin-addr-1 pml4-table-base-addr x86))
		(physical-address-p pml4-table-base-addr)
		(canonical-address-p lin-addr-1)
		(canonical-address-p lin-addr-2)
		(equal (loghead 12 pml4-table-base-addr) 0)
		(x86p x86))
	   (ia32e-la-to-pa-pml4-table-entry-validp
	    lin-addr-1 pml4-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
	    (mv-nth 2
		    (ia32e-la-to-pa-page-dir-ptr-table
		     lin-addr-2 ptr-table-base-addr wp-2 smep-2
		     nxe-2 r-w-x-2 cpl-2 x86))))
  :do-not '(preprocess)
  :use ((:instance equality-of-pml4-table-entry-addr)
	(:instance equality-of-page-dir-ptr-table-entry-addr))
  :in-theory (e/d
	      (page-dir-ptr-table-components-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-dir-ptr-table-1G-pages
	       pml4-table-components-equal-rm-low-64-of-pml4-entry-addr-via-pml4-table-1G-pages)
	      (ia32e-la-to-pa-pml4-table-entry-validp
	       not
	       mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-1g-pages
	       mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1g-pages
	       acl2::mv-nth-cons-meta
	       unsigned-byte-p
	       signed-byte-p)))

(defrule two-page-table-walks-ia32e-la-to-pa-pml4-table-1G-pages-same-entry-different-addrs
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr-1 pml4-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr-2 pml4-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr-1 pml4-table-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr-1 ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

		;; So that pml4 table entries are the same...
		(equal (part-select lin-addr-1 :low 39 :high 47)
		       (part-select lin-addr-2 :low 39 :high 47))
		;; So that the ptr table entries are the same...
		(equal (part-select lin-addr-1 :low 30 :high 38)
		       (part-select lin-addr-2 :low 30 :high 38))
		;; So that the physical addresses are different...
		(not (equal (part-select lin-addr-1 :low 0 :high 29)
			    (part-select lin-addr-2 :low 0 :high 29)))

		(pairwise-disjoint-p
		 (translation-governing-addresses-for-pml4-table
		  lin-addr-1 pml4-table-base-addr x86))
		(physical-address-p pml4-table-base-addr)
		(canonical-address-p lin-addr-1)
		(canonical-address-p lin-addr-2)
		(equal (loghead 12 pml4-table-base-addr) 0)
		(x86p x86))
	   (equal
	    (mv-nth
	     1
	     (ia32e-la-to-pa-pml4-table
	      lin-addr-1 pml4-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
	      (mv-nth
	       2
	       (ia32e-la-to-pa-pml4-table
		lin-addr-2 pml4-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
	    (mv-nth
	     1
	     (ia32e-la-to-pa-pml4-table
	      lin-addr-1 pml4-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86))))
  :do-not '(preprocess)
  :use ((:instance equality-of-pml4-table-entry-addr)
	(:instance equality-of-page-dir-ptr-table-entry-addr))
  :in-theory (e/d (page-size-from-re-reading-page-dir-ptr-table-entry-given-pml4-entry-validp-1G-pages
		   logtail-12-of-reading-page-dir-ptr-table-entry-from-state-after-page-dir-ptr-table-given-pml4-table-validp-1G-pages
		   re-read-entry-still-pml4-table-valid-page-dir-ptr-table-1G-pages)
		  (ia32e-la-to-pa-pml4-table-entry-validp
		   mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-1g-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1g-pages
		   mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
		   member-p-cons
		   disjoint-p-cons
		   not
		   unsigned-byte-p
		   signed-byte-p)))

;; 2M pages:

(defruled page-size-from-re-reading-page-dir-ptr-table-entry-given-pml4-entry-validp-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)

		;; (pairwise-disjoint-p
		;;  (list (addr-range 8 pml4-entry-addr)
		;;        (addr-range 8 ptr-table-entry-addr)
		;;        (addr-range 8 page-directory-entry-addr)))
		(pairwise-disjoint-p
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))
		(physical-address-p pml4-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 pml4-base-addr) 0)
		(x86p x86))
	   (equal (ia32e-page-tables-slice
		   :ps
		   (rm-low-64
		    ptr-table-entry-addr
		    (mv-nth 2
			    (ia32e-la-to-pa-page-dir-ptr-table
			     lin-addr ptr-table-base-addr wp smep
			     nxe r-w-x cpl x86))))
		  0))
  :do-not '(preprocess)
  :in-theory (e/d* (
		    rm-low-64-and-page-dir-ptr-table-2M-pages)
		   (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		    mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
		    mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2m-pages
		    subset-p-two-addr-ranges
		    disjoint-p-two-addr-ranges-thm-3
		    disjoint-p-two-addr-ranges-thm-2
		    disjoint-p-two-addr-ranges-thm-1
		    <-preserved-by-adding-<-*pseudo-page-size-in-bytes*-commuted
		    <-preserved-by-adding-<-*pseudo-page-size-in-bytes*
		    not
		    unsigned-byte-p
		    signed-byte-p)))

(defruled page-size-from-reading-page-directory-entry-from-state-after-page-dir-ptr-table-given-pml4-entry-validp-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)

		;; (pairwise-disjoint-p
		;;  (list (addr-range 8 pml4-entry-addr)
		;;        (addr-range 8 ptr-table-entry-addr)
		;;        (addr-range 8 page-directory-entry-addr)))
		(pairwise-disjoint-p
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))
		(physical-address-p pml4-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 pml4-base-addr) 0)
		(x86p x86))
	   (equal (ia32e-page-tables-slice
		   :ps
		   (rm-low-64
		    page-directory-entry-addr
		    (mv-nth 2
			    (ia32e-la-to-pa-page-dir-ptr-table
			     lin-addr ptr-table-base-addr wp smep
			     nxe r-w-x cpl x86))))
		  1))
  :do-not '(preprocess)
  :in-theory (e/d* (rm-low-64-and-page-dir-ptr-table-2M-pages
		    rm-low-64-and-page-directory-2M-pages)
		   (subset-p-two-addr-ranges
		    disjoint-p-two-addr-ranges-thm-3
		    disjoint-p-two-addr-ranges-thm-2
		    disjoint-p-two-addr-ranges-thm-1
		    <-preserved-by-adding-<-*pseudo-page-size-in-bytes*-commuted
		    <-preserved-by-adding-<-*pseudo-page-size-in-bytes*
		    not
		    unsigned-byte-p
		    signed-byte-p)))

(defruled logtail-12-of-reading-page-dir-ptr-table-entry-from-state-after-page-dir-ptr-table-given-pml4-table-validp-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)

		;; (pairwise-disjoint-p
		;;  (list (addr-range 8 pml4-entry-addr)
		;;        (addr-range 8 ptr-table-entry-addr)
		;;        (addr-range 8 page-directory-entry-addr)))
		(pairwise-disjoint-p
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))
		(physical-address-p pml4-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 pml4-base-addr) 0)
		(x86p x86))
	   (equal (logtail 12
			   (rm-low-64
			    ptr-table-entry-addr
			    (mv-nth 2
				    (ia32e-la-to-pa-page-dir-ptr-table
				     lin-addr ptr-table-base-addr wp smep
				     nxe r-w-x cpl x86))))
		  (logtail 12 (rm-low-64 ptr-table-entry-addr x86))))
  :do-not '(preprocess)
  :in-theory (e/d* (
		    rm-low-64-and-page-dir-ptr-table-2M-pages
		    page-size-from-re-reading-page-dir-ptr-table-entry-given-pml4-entry-validp-2M-pages
		    page-size-from-reading-page-directory-entry-from-state-after-page-dir-ptr-table-given-pml4-entry-validp-2M-pages)
		   (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		    mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
		    mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2m-pages
		    subset-p-two-addr-ranges
		    disjoint-p-two-addr-ranges-thm-3
		    disjoint-p-two-addr-ranges-thm-2
		    disjoint-p-two-addr-ranges-thm-1
		    <-preserved-by-adding-<-*pseudo-page-size-in-bytes*-commuted
		    <-preserved-by-adding-<-*pseudo-page-size-in-bytes*
		    not
		    unsigned-byte-p
		    signed-byte-p)))

(defruled re-read-entry-still-pml4-table-valid-page-dir-ptr-table-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)

		;; (pairwise-disjoint-p
		;;  (list (addr-range 8 pml4-entry-addr)
		;;        (addr-range 8 ptr-table-entry-addr)
		;;        (addr-range 8 page-directory-entry-addr)))

		(pairwise-disjoint-p
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))

		(physical-address-p pml4-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 pml4-base-addr) 0)
		(x86p x86))

	   (ia32e-la-to-pa-pml4-table-entry-validp
	    lin-addr pml4-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
	    (mv-nth
	     2
	     (ia32e-la-to-pa-page-dir-ptr-table
	      lin-addr ptr-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))

  :do-not '(preprocess)
  :in-theory (e/d
	      (page-dir-ptr-table-components-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-dir-ptr-table-2M-pages
	       page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-page-dir-ptr-table-2M-pages
	       logtail-12-of-reading-page-dir-ptr-table-entry-from-state-after-page-dir-ptr-table-given-pml4-table-validp-2M-pages
	       page-size-from-re-reading-page-dir-ptr-table-entry-given-pml4-entry-validp-2M-pages
	       page-size-from-reading-page-directory-entry-from-state-after-page-dir-ptr-table-given-pml4-entry-validp-2M-pages)
	      (ia32e-la-to-pa-pml4-table-entry-validp
	       not
	       mv-nth-2-no-error-ia32e-la-to-pa-pml4-table
	       mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
	       mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
	       acl2::mv-nth-cons-meta
	       subset-p-two-addr-ranges
	       disjoint-p-two-addr-ranges-thm-3
	       disjoint-p-two-addr-ranges-thm-2
	       disjoint-p-two-addr-ranges-thm-1
	       <-preserved-by-adding-<-*pseudo-page-size-in-bytes*-commuted
	       <-preserved-by-adding-<-*pseudo-page-size-in-bytes*
	       unsigned-byte-p
	       signed-byte-p)))

(defrule two-page-table-walks-ia32e-la-to-pa-pml4-table-2M-pages-same-addresses

  ;; Key lemmas needed:

  ;; mv-nth-2-no-error-ia32e-la-to-pa-pml4-table
  ;; re-read-entry-still-pml4-table-valid-page-dir-ptr-table-2M-pages
  ;; reading-entry-with-accessed-bit-set-ia32e-la-to-pa-pml4-table-2M-pages
  ;; mv-nth-1-no-error-ia32e-la-to-pa-pml4-table
  ;; pml4-table-entry-validp-to-page-dir-ptr-entry-validp
  ;; two-page-table-walks-ia32e-la-to-pa-dir-ptr-table-2M-pages-same-addresses

  ;; Note that for this theorem, we also need:
  ;; page-size-from-re-reading-page-dir-ptr-table-entry-given-pml4-entry-validp-2M-pages
  ;; page-size-from-reading-page-directory-entry-from-state-after-page-dir-ptr-table-given-pml4-entry-validp-2M-pages
  ;; logtail-12-of-reading-page-dir-ptr-table-entry-from-state-after-page-dir-ptr-table-given-pml4-table-validp-2M-pages

  ;; I discovered that I needed the additional lemmas by:
  ;; (acl2::why reading-entry-with-accessed-bit-set-ia32e-la-to-pa-pml4-table-2M-pages)
  ;; (acl2::why relating-validity-of-two-entries-in-two-x86-states-wrt-pml4-table-2M-pages)

  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)

		;; (pairwise-disjoint-p
		;;  (list (addr-range 8 pml4-entry-addr)
		;;        (addr-range 8 ptr-table-entry-addr)
		;;        (addr-range 8 page-directory-entry-addr)))

		(pairwise-disjoint-p
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))

		(physical-address-p pml4-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 pml4-base-addr) 0)
		(x86p x86))
	   (equal
	    (mv-nth
	     1
	     (ia32e-la-to-pa-pml4-table
	      lin-addr pml4-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
	      (mv-nth
	       2
	       (ia32e-la-to-pa-pml4-table
		lin-addr pml4-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
	    (mv-nth
	     1
	     (ia32e-la-to-pa-pml4-table
	      lin-addr pml4-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86))))
  :do-not '(preprocess)
  :in-theory (e/d (page-dir-ptr-table-components-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-dir-ptr-table-2M-pages
		   page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-page-dir-ptr-table-2M-pages
		   re-read-entry-still-pml4-table-valid-page-dir-ptr-table-2M-pages
		   page-size-from-re-reading-page-dir-ptr-table-entry-given-pml4-entry-validp-2M-pages
		   page-size-from-reading-page-directory-entry-from-state-after-page-dir-ptr-table-given-pml4-entry-validp-2M-pages
		   logtail-12-of-reading-page-dir-ptr-table-entry-from-state-after-page-dir-ptr-table-given-pml4-table-validp-2M-pages)
		  (ia32e-la-to-pa-pml4-table-entry-validp
		   member-p-cons
		   disjoint-p-cons
		   mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
		   subset-p-two-addr-ranges
		   disjoint-p-two-addr-ranges-thm-3
		   disjoint-p-two-addr-ranges-thm-2
		   disjoint-p-two-addr-ranges-thm-1
		   <-preserved-by-adding-<-*pseudo-page-size-in-bytes*-commuted
		   <-preserved-by-adding-<-*pseudo-page-size-in-bytes*
		   not
		   unsigned-byte-p
		   signed-byte-p)))

(defrule two-page-table-walks-ia32e-la-to-pa-pml4-table-2M-pages-same-entry-different-addrs
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr-1 pml4-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr-2 pml4-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr-1 pml4-table-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr-1 ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr-1 page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)
		(pairwise-disjoint-p
		 (translation-governing-addresses-for-pml4-table
		  lin-addr-1 pml4-table-base-addr x86))

		;; So that pml4 table entries are the same...
		(equal (part-select lin-addr-1 :low 39 :high 47)
		       (part-select lin-addr-2 :low 39 :high 47))
		;; So that the ptr table entries are the same...
		(equal (part-select lin-addr-1 :low 30 :high 38)
		       (part-select lin-addr-2 :low 30 :high 38))
		;; So that the page directory entries are the same...
		(equal (part-select lin-addr-1 :low 21 :high 29)
		       (part-select lin-addr-2 :low 21 :high 29))
		;; So that the physical address is different...
		(not (equal (part-select lin-addr-1 :low 0 :high 20)
			    (part-select lin-addr-2 :low 0 :high 20)))

		(physical-address-p pml4-table-base-addr)
		(canonical-address-p lin-addr-1)
		(canonical-address-p lin-addr-2)
		(equal (loghead 12 pml4-table-base-addr) 0)
		(x86p x86))
	   (equal
	    (mv-nth
	     1
	     (ia32e-la-to-pa-pml4-table
	      lin-addr-1 pml4-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
	      (mv-nth
	       2
	       (ia32e-la-to-pa-pml4-table
		lin-addr-2 pml4-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
	    (mv-nth
	     1
	     (ia32e-la-to-pa-pml4-table
	      lin-addr-1 pml4-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86))))
  :do-not '(preprocess)
  :use ((:instance equality-of-pml4-table-entry-addr)
	(:instance equality-of-page-dir-ptr-table-entry-addr)
	(:instance equality-of-page-directory-entry-addr))
  :in-theory (e/d (page-dir-ptr-table-components-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-dir-ptr-table-2M-pages
		   page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-page-dir-ptr-table-2M-pages
		   re-read-entry-still-pml4-table-valid-page-dir-ptr-table-2M-pages
		   page-size-from-re-reading-page-dir-ptr-table-entry-given-pml4-entry-validp-2M-pages
		   page-size-from-reading-page-directory-entry-from-state-after-page-dir-ptr-table-given-pml4-entry-validp-2M-pages
		   logtail-12-of-reading-page-dir-ptr-table-entry-from-state-after-page-dir-ptr-table-given-pml4-table-validp-2M-pages)
		  (ia32e-la-to-pa-pml4-table-entry-validp
		   mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-1g-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1g-pages
		   mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
		   member-p-cons
		   disjoint-p-cons
		   not
		   unsigned-byte-p
		   signed-byte-p)))

;; 4K pages:

(defruled page-size-from-re-reading-page-dir-ptr-table-entry-given-pml4-entry-validp-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))


		;; (pairwise-disjoint-p
		;;  (list (addr-range 8 pml4-entry-addr)
		;;        (addr-range 8 ptr-table-entry-addr)
		;;        (addr-range 8 page-directory-entry-addr)
		;;        (addr-range 8 page-table-entry-addr)))

		(pairwise-disjoint-p
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))

		(physical-address-p pml4-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 pml4-base-addr) 0)
		(x86p x86))
	   (equal (ia32e-page-tables-slice
		   :ps
		   (rm-low-64
		    ptr-table-entry-addr
		    (mv-nth 2
			    (ia32e-la-to-pa-page-dir-ptr-table
			     lin-addr ptr-table-base-addr wp smep
			     nxe r-w-x cpl x86))))
		  0))
  :do-not '(preprocess)
  :in-theory (e/d* (
		    rm-low-64-and-page-dir-ptr-table-4K-pages)
		   (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		    mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
		    mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2m-pages
		    subset-p-two-addr-ranges
		    disjoint-p-two-addr-ranges-thm-3
		    disjoint-p-two-addr-ranges-thm-2
		    disjoint-p-two-addr-ranges-thm-1
		    disjoint-p-two-addr-ranges-thm-0
		    <-preserved-by-adding-<-*pseudo-page-size-in-bytes*-commuted
		    <-preserved-by-adding-<-*pseudo-page-size-in-bytes*
		    not
		    unsigned-byte-p
		    signed-byte-p)))

(defruled page-size-from-reading-page-directory-entry-from-state-after-page-dir-ptr-table-given-pml4-entry-validp-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))


		;; (pairwise-disjoint-p
		;;  (list (addr-range 8 pml4-entry-addr)
		;;        (addr-range 8 ptr-table-entry-addr)
		;;        (addr-range 8 page-directory-entry-addr)
		;;        (addr-range 8 page-table-entry-addr)))
		(pairwise-disjoint-p
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))


		(physical-address-p pml4-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 pml4-base-addr) 0)
		(x86p x86))
	   (equal (ia32e-page-tables-slice
		   :ps
		   (rm-low-64
		    page-directory-entry-addr
		    (mv-nth 2
			    (ia32e-la-to-pa-page-dir-ptr-table
			     lin-addr ptr-table-base-addr wp smep
			     nxe r-w-x cpl x86))))
		  0))
  :do-not '(preprocess)
  :in-theory (e/d* (rm-low-64-and-page-dir-ptr-table-4K-pages
		    rm-low-64-and-page-directory-4K-pages
		    rm-low-64-and-page-table
		    ia32e-la-to-pa-page-dir-ptr-table-entry-validp)
		   (mv-nth-2-no-error-ia32e-la-to-pa-page-table
		    subset-p-two-addr-ranges
		    disjoint-p-two-addr-ranges-thm-3
		    disjoint-p-two-addr-ranges-thm-2
		    disjoint-p-two-addr-ranges-thm-1
		    disjoint-p-two-addr-ranges-thm-0
		    <-preserved-by-adding-<-*pseudo-page-size-in-bytes*-commuted
		    <-preserved-by-adding-<-*pseudo-page-size-in-bytes*
		    not
		    unsigned-byte-p
		    signed-byte-p)))

(defruled logtail-12-of-reading-page-dir-ptr-table-entry-from-state-after-page-dir-ptr-table-given-pml4-table-validp-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))


		;; (pairwise-disjoint-p
		;;  (list (addr-range 8 pml4-entry-addr)
		;;        (addr-range 8 ptr-table-entry-addr)
		;;        (addr-range 8 page-directory-entry-addr)
		;;        (addr-range 8 page-table-entry-addr)))
		(pairwise-disjoint-p
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))

		(physical-address-p pml4-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 pml4-base-addr) 0)
		(x86p x86))
	   (equal (logtail 12
			   (rm-low-64
			    ptr-table-entry-addr
			    (mv-nth 2
				    (ia32e-la-to-pa-page-dir-ptr-table
				     lin-addr ptr-table-base-addr wp smep
				     nxe r-w-x cpl x86))))
		  (logtail 12 (rm-low-64 ptr-table-entry-addr x86))))
  :do-not '(preprocess)
  :in-theory (e/d* (rm-low-64-and-page-dir-ptr-table-4K-pages
		    page-size-from-re-reading-page-dir-ptr-table-entry-given-pml4-entry-validp-4K-pages
		    page-size-from-reading-page-directory-entry-from-state-after-page-dir-ptr-table-given-pml4-entry-validp-4K-pages)
		   (ia32e-la-to-pa-page-dir-ptr-table-entry-validp
		    mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
		    mv-nth-2-no-error-ia32e-la-to-pa-page-directory-2m-pages
		    subset-p-two-addr-ranges
		    disjoint-p-two-addr-ranges-thm-3
		    disjoint-p-two-addr-ranges-thm-2
		    disjoint-p-two-addr-ranges-thm-1
		    disjoint-p-two-addr-ranges-thm-0
		    <-preserved-by-adding-<-*pseudo-page-size-in-bytes*-commuted
		    <-preserved-by-adding-<-*pseudo-page-size-in-bytes*
		    not
		    unsigned-byte-p
		    signed-byte-p)))

(defruled re-read-entry-still-pml4-table-valid-page-dir-ptr-table-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))

		;; (pairwise-disjoint-p
		;;  (list (addr-range 8 pml4-entry-addr)
		;;        (addr-range 8 ptr-table-entry-addr)
		;;        (addr-range 8 page-directory-entry-addr)
		;;        (addr-range 8 page-table-entry-addr)))
		(pairwise-disjoint-p
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))

		(physical-address-p pml4-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 pml4-base-addr) 0)
		(x86p x86))

	   (ia32e-la-to-pa-pml4-table-entry-validp
	    lin-addr pml4-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
	    (mv-nth
	     2
	     (ia32e-la-to-pa-page-dir-ptr-table
	      lin-addr ptr-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))

  :do-not '(preprocess)
  :in-theory (e/d
	      (page-dir-ptr-table-components-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-dir-ptr-table-4K-pages
	       page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-page-dir-ptr-table-4K-pages
	       page-table-components-equal-rm-low-64-of-page-table-entry-addr-via-page-dir-ptr-table-4K-pages
	       logtail-12-of-reading-page-dir-ptr-table-entry-from-state-after-page-dir-ptr-table-given-pml4-table-validp-4K-pages
	       page-size-from-re-reading-page-dir-ptr-table-entry-given-pml4-entry-validp-4K-pages
	       page-size-from-reading-page-directory-entry-from-state-after-page-dir-ptr-table-given-pml4-entry-validp-4K-pages)
	      (ia32e-la-to-pa-pml4-table-entry-validp
	       not
	       mv-nth-2-no-error-ia32e-la-to-pa-pml4-table
	       mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
	       mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
	       acl2::mv-nth-cons-meta
	       subset-p-two-addr-ranges
	       disjoint-p-two-addr-ranges-thm-3
	       disjoint-p-two-addr-ranges-thm-2
	       disjoint-p-two-addr-ranges-thm-1
	       disjoint-p-two-addr-ranges-thm-0
	       <-preserved-by-adding-<-*pseudo-page-size-in-bytes*-commuted
	       <-preserved-by-adding-<-*pseudo-page-size-in-bytes*
	       unsigned-byte-p
	       signed-byte-p)))

(defruled logtail-12-of-reading-page-directory-entry-from-state-after-page-dir-ptr-table-given-pml4-table-validp-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))


		;; (pairwise-disjoint-p
		;;  (list (addr-range 8 pml4-entry-addr)
		;;        (addr-range 8 ptr-table-entry-addr)
		;;        (addr-range 8 page-directory-entry-addr)
		;;        (addr-range 8 page-table-entry-addr)))
		(pairwise-disjoint-p
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))


		(physical-address-p pml4-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 pml4-base-addr) 0)
		(x86p x86))
	   (equal (logtail 12
			   (rm-low-64
			    page-directory-entry-addr
			    (mv-nth 2
				    (ia32e-la-to-pa-page-dir-ptr-table
				     lin-addr ptr-table-base-addr wp smep
				     nxe r-w-x cpl x86))))
		  (logtail 12 (rm-low-64 page-directory-entry-addr x86))))
  :do-not '(preprocess)
  :in-theory (e/d* (logtail-12-of-reading-page-directory-entry-from-state-after-page-directory-given-page-dir-ptr-table-validp
		    rm-low-64-and-page-dir-ptr-table-4K-pages
		    rm-low-64-and-page-directory-4K-pages
		    page-size-from-re-reading-page-dir-ptr-table-entry-given-pml4-entry-validp-4K-pages
		    page-size-from-reading-page-directory-entry-from-state-after-page-dir-ptr-table-given-pml4-entry-validp-4K-pages
		    ia32e-la-to-pa-page-dir-ptr-table-entry-validp)
		   (mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
		    subset-p-two-addr-ranges
		    disjoint-p-two-addr-ranges-thm-3
		    disjoint-p-two-addr-ranges-thm-2
		    disjoint-p-two-addr-ranges-thm-1
		    disjoint-p-two-addr-ranges-thm-0
		    <-preserved-by-adding-<-*pseudo-page-size-in-bytes*-commuted
		    <-preserved-by-adding-<-*pseudo-page-size-in-bytes*
		    not
		    unsigned-byte-p
		    signed-byte-p)))

(defrule two-page-table-walks-ia32e-la-to-pa-pml4-table-4K-pages-same-addresses

  ;; Key lemmas:

  ;; mv-nth-2-no-error-ia32e-la-to-pa-pml4-table
  ;; re-read-entry-still-pml4-table-valid-page-dir-ptr-table-4K-pages
  ;; reading-entry-with-accessed-bit-set-ia32e-la-to-pa-pml4-table-4K-pages
  ;; mv-nth-1-no-error-ia32e-la-to-pa-pml4-table
  ;; pml4-table-entry-validp-to-page-dir-ptr-entry-validp
  ;; two-page-table-walks-ia32e-la-to-pa-dir-ptr-table-4K-pages-same-addresses

  ;; Note that for this theorem, we also need:
  ;; page-size-from-re-reading-page-dir-ptr-table-entry-given-pml4-entry-validp-4K-pages
  ;; page-size-from-reading-page-directory-entry-from-state-after-page-dir-ptr-table-given-pml4-entry-validp-4K-pages
  ;; logtail-12-of-reading-page-dir-ptr-table-entry-from-state-after-page-dir-ptr-table-given-pml4-table-validp-4K-pages
  ;; logtail-12-of-reading-page-directory-entry-from-state-after-page-dir-ptr-table-given-pml4-table-validp-4K-pages

  ;; I discovered that I needed the additional lemmas by:
  ;; (acl2::why reading-entry-with-accessed-bit-set-ia32e-la-to-pa-pml4-table-4K-pages)

  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))

		;; (pairwise-disjoint-p
		;;  (list (addr-range 8 pml4-entry-addr)
		;;        (addr-range 8 ptr-table-entry-addr)
		;;        (addr-range 8 page-directory-entry-addr)
		;;        (addr-range 8 page-table-entry-addr)))
		(pairwise-disjoint-p
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))

		(physical-address-p pml4-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 pml4-base-addr) 0)
		(x86p x86))
	   (equal
	    (mv-nth
	     1
	     (ia32e-la-to-pa-pml4-table
	      lin-addr pml4-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
	      (mv-nth
	       2
	       (ia32e-la-to-pa-pml4-table
		lin-addr pml4-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
	    (mv-nth
	     1
	     (ia32e-la-to-pa-pml4-table
	      lin-addr pml4-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86))))
  :do-not '(preprocess)
  :in-theory (e/d
	      (pml4-table-components-equal-rm-low-64-of-pml4-entry-addr-via-pml4-table-4K-pages
	       page-dir-ptr-table-components-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-dir-ptr-table-4K-pages
	       page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-page-dir-ptr-table-4K-pages
	       page-table-components-equal-rm-low-64-of-page-table-entry-addr-via-page-dir-ptr-table-4K-pages
	       re-read-entry-still-pml4-table-valid-page-dir-ptr-table-4K-pages
	       page-size-from-re-reading-page-dir-ptr-table-entry-given-pml4-entry-validp-4K-pages
	       page-size-from-reading-page-directory-entry-from-state-after-page-dir-ptr-table-given-pml4-entry-validp-4K-pages
	       logtail-12-of-reading-page-dir-ptr-table-entry-from-state-after-page-dir-ptr-table-given-pml4-table-validp-4K-pages
	       logtail-12-of-reading-page-directory-entry-from-state-after-page-dir-ptr-table-given-pml4-table-validp-4K-pages)
	      (ia32e-la-to-pa-pml4-table-entry-validp
	       member-p-cons
	       disjoint-p-cons
	       mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
	       mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
	       mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
	       mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
	       subset-p-two-addr-ranges
	       disjoint-p-two-addr-ranges-thm-3
	       disjoint-p-two-addr-ranges-thm-2
	       disjoint-p-two-addr-ranges-thm-1
	       disjoint-p-two-addr-ranges-thm-0
	       <-preserved-by-adding-<-*pseudo-page-size-in-bytes*-commuted
	       <-preserved-by-adding-<-*pseudo-page-size-in-bytes*
	       not
	       unsigned-byte-p
	       signed-byte-p)))

(defrule two-page-table-walks-ia32e-la-to-pa-pml4-table-4K-pages-same-entry-different-addrs
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr-1 pml4-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr-2 pml4-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr-1 pml4-table-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr-1 ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr-1 page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr-1 page-table-base-addr))

		;; So that pml4 table entries are the same...
		(equal (part-select lin-addr-1 :low 39 :high 47)
		       (part-select lin-addr-2 :low 39 :high 47))
		;; So that the ptr table entries are the same...
		(equal (part-select lin-addr-1 :low 30 :high 38)
		       (part-select lin-addr-2 :low 30 :high 38))
		;; So that the page directory entries are the same...
		(equal (part-select lin-addr-1 :low 21 :high 29)
		       (part-select lin-addr-2 :low 21 :high 29))
		;; So that the page table entries are the same...
		(equal (part-select lin-addr-1 :low 12 :high 20)
		       (part-select lin-addr-2 :low 12 :high 20))
		;; So that the physical address is different...
		(not (equal (part-select lin-addr-1 :low 0 :width 12)
			    (part-select lin-addr-2 :low 0 :width 12)))

		(pairwise-disjoint-p
		 (translation-governing-addresses-for-pml4-table
		  lin-addr-1 pml4-table-base-addr x86))

		(physical-address-p pml4-table-base-addr)
		(canonical-address-p lin-addr-1)
		(canonical-address-p lin-addr-2)
		(equal (loghead 12 pml4-table-base-addr) 0)
		(x86p x86))
	   (equal
	    (mv-nth
	     1
	     (ia32e-la-to-pa-pml4-table
	      lin-addr-1 pml4-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
	      (mv-nth
	       2
	       (ia32e-la-to-pa-pml4-table
		lin-addr-2 pml4-table-base-addr wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
	    (mv-nth
	     1
	     (ia32e-la-to-pa-pml4-table
	      lin-addr-1 pml4-table-base-addr wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86))))
  :do-not '(preprocess)
  :use ((:instance equality-of-pml4-table-entry-addr)
	(:instance equality-of-page-dir-ptr-table-entry-addr)
	(:instance equality-of-page-directory-entry-addr)
	(:instance equality-of-page-table-entry-addr))
  :in-theory (e/d
	      (pml4-table-components-equal-rm-low-64-of-pml4-entry-addr-via-pml4-table-4K-pages
	       page-dir-ptr-table-components-equal-rm-low-64-of-page-dir-ptr-table-entry-addr-via-page-dir-ptr-table-4K-pages
	       page-directory-components-equal-rm-low-64-of-page-directory-entry-addr-via-page-dir-ptr-table-4K-pages
	       page-table-components-equal-rm-low-64-of-page-table-entry-addr-via-page-dir-ptr-table-4K-pages
	       re-read-entry-still-pml4-table-valid-page-dir-ptr-table-4K-pages
	       page-size-from-re-reading-page-dir-ptr-table-entry-given-pml4-entry-validp-4K-pages
	       page-size-from-reading-page-directory-entry-from-state-after-page-dir-ptr-table-given-pml4-entry-validp-4K-pages
	       logtail-12-of-reading-page-dir-ptr-table-entry-from-state-after-page-dir-ptr-table-given-pml4-table-validp-4K-pages
	       logtail-12-of-reading-page-directory-entry-from-state-after-page-dir-ptr-table-given-pml4-table-validp-4K-pages)
	      (ia32e-la-to-pa-pml4-table-entry-validp
	       member-p-cons
	       disjoint-p-cons
	       mv-nth-1-no-error-ia32e-la-to-pa-page-directory-4K-pages
	       mv-nth-2-no-error-ia32e-la-to-pa-page-directory-4K-pages
	       mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
	       mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
	       subset-p-two-addr-ranges
	       disjoint-p-two-addr-ranges-thm-3
	       disjoint-p-two-addr-ranges-thm-2
	       disjoint-p-two-addr-ranges-thm-1
	       disjoint-p-two-addr-ranges-thm-0
	       <-preserved-by-adding-<-*pseudo-page-size-in-bytes*-commuted
	       <-preserved-by-adding-<-*pseudo-page-size-in-bytes*
	       not
	       unsigned-byte-p
	       signed-byte-p)))


;; ......................................................................
;; Two pml4 table walks theorem --- different entries:
;; ......................................................................

(defrule two-page-table-walks-ia32e-la-to-pa-pml4-table-different-entries

  ;; Key lemmas:

  ;; mv-nth-2-no-error-ia32e-la-to-pa-pml4-table
  ;; mv-nth-1-no-error-ia32e-la-to-pa-pml4-table-1G-pages-with-disjoint-wm-low-64
  ;; mv-nth-1-no-error-ia32e-la-to-pa-pml4-table-2M-pages-with-disjoint-wm-low-64
  ;; mv-nth-1-no-error-ia32e-la-to-pa-pml4-table-4K-pages-with-disjoint-wm-low-64

  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr-1 pml4-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr-2 pml4-base-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)

		(pairwise-disjoint-p
		 (append
		  (translation-governing-addresses-for-pml4-table
		   lin-addr-2 pml4-base-addr-2 x86)
		  (translation-governing-addresses-for-pml4-table
		   lin-addr-1 pml4-base-addr-1 x86)))

		(physical-address-p pml4-base-addr-1)
		(canonical-address-p lin-addr-1)
		(equal (loghead 12 pml4-base-addr-1) 0)

		(physical-address-p pml4-base-addr-2)
		(canonical-address-p lin-addr-2)
		(equal (loghead 12 pml4-base-addr-2) 0)

		(x86p x86))
	   (equal
	    (mv-nth
	     1
	     (ia32e-la-to-pa-pml4-table
	      lin-addr-1 pml4-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
	      (mv-nth
	       2
	       (ia32e-la-to-pa-pml4-table
		lin-addr-2 pml4-base-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
	    (mv-nth
	     1
	     (ia32e-la-to-pa-pml4-table
	      lin-addr-1 pml4-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
	      x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ifix
		   ia32e-la-to-pa-page-directory-entry-components-equal-p
		   ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p)
		  (ia32e-la-to-pa-pml4-table-entry-validp
		   page-dir-ptr-entry-validp-to-page-directory-entry-validp
		   mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
		   mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
		   reading-entry-with-accessed-bit-set-ia32e-la-to-pa-pml4-table-4k-pages
		   addr-range
		   member-p-cons
		   disjoint-p-cons
		   not
		   unsigned-byte-p
		   signed-byte-p)))

;; ......................................................................
;; More theorems about validity of pml4 table entries being preserved
;; when the translation-governing addresses are disjoint:
;; ......................................................................

(defrule validity-preserved-same-x86-state-disjoint-addresses-wrt-pml4-table
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr-1 pml4-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr-2 pml4-base-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)

		(pairwise-disjoint-p
		 (append
		  (translation-governing-addresses-for-pml4-table
		   lin-addr-2 pml4-base-addr-2 x86)
		  (translation-governing-addresses-for-pml4-table
		   lin-addr-1 pml4-base-addr-1 x86)))

		(physical-address-p pml4-base-addr-1)
		(canonical-address-p lin-addr-1)
		(equal (loghead 12 pml4-base-addr-1) 0)

		(physical-address-p pml4-base-addr-2)
		(canonical-address-p lin-addr-2)
		(equal (loghead 12 pml4-base-addr-2) 0)

		(x86p x86))

	   (ia32e-la-to-pa-pml4-table-entry-validp
	    lin-addr-1 pml4-base-addr-1 wp-1 smep-1 nxe-1 r-w-x-1 cpl-1
	    (mv-nth
	     2
	     (ia32e-la-to-pa-pml4-table
	      lin-addr-2 pml4-base-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86))))
  :in-theory (e/d (ifix
		   ia32e-la-to-pa-page-directory-entry-components-equal-p
		   ia32e-la-to-pa-page-dir-ptr-table-entry-components-equal-p)
		  (ia32e-la-to-pa-pml4-table-entry-validp
		   page-dir-ptr-entry-validp-to-page-directory-entry-validp
		   mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
		   mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
		   member-p-cons
		   disjoint-p-cons
		   not
		   unsigned-byte-p
		   signed-byte-p)))

;; ......................................................................
;; Translation-Governing-Addresses-For-PML4-Table and
;; ia32e-la-to-pa-pml4-table-entry:
;; ......................................................................

;; 1G pages

(defruled logtail-12-of-reading-pml4-entry-from-state-after-page-dir-ptr-table-given-pml4-table-validp-1G-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)
		(pairwise-disjoint-p
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))
		(physical-address-p pml4-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 pml4-base-addr) 0)
		(x86p x86))
	   (equal
	    (logtail 12
		     (rm-low-64 pml4-entry-addr
				(mv-nth 2
					(ia32e-la-to-pa-page-dir-ptr-table
					 lin-addr ptr-table-base-addr wp smep
					 nxe r-w-x cpl x86))))
	    (logtail 12
		     (rm-low-64 pml4-entry-addr x86))))
  :do-not '(preprocess)
  :in-theory (e/d (rm-low-64-and-ia32e-la-to-pa-pml4-table-1G-pages)
		  (not
		   mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
		   mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
		   unsigned-byte-p
		   signed-byte-p)))

;; 2M pages:

(defruled logtail-12-of-reading-pml4-entry-from-state-after-page-dir-ptr-table-given-pml4-table-validp-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)

		(pairwise-disjoint-p
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))

		(physical-address-p pml4-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 pml4-base-addr) 0)
		(x86p x86))
	   (equal
	    (logtail 12
		     (rm-low-64 pml4-entry-addr
				(mv-nth 2
					(ia32e-la-to-pa-page-dir-ptr-table
					 lin-addr ptr-table-base-addr wp smep
					 nxe r-w-x cpl x86))))
	    (logtail 12
		     (rm-low-64 pml4-entry-addr x86))))
  :do-not '(preprocess)
  :in-theory (e/d (rm-low-64-and-ia32e-la-to-pa-pml4-table-2M-pages)
		  (not
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
		   unsigned-byte-p
		   signed-byte-p)))

;; 4K pages:

(defruled logtail-12-of-reading-pml4-entry-from-state-after-page-dir-ptr-table-given-pml4-table-validp-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))


		(pairwise-disjoint-p
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))

		(physical-address-p pml4-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 pml4-base-addr) 0)
		(x86p x86))
	   (equal
	    (logtail 12
		     (rm-low-64 pml4-entry-addr
				(mv-nth 2
					(ia32e-la-to-pa-page-dir-ptr-table
					 lin-addr ptr-table-base-addr wp smep
					 nxe r-w-x cpl x86))))
	    (logtail 12
		     (rm-low-64 pml4-entry-addr x86))))

  :do-not '(preprocess)
  :in-theory (e/d (rm-low-64-and-ia32e-la-to-pa-pml4-table-4K-pages)
		  (not
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4K-or-2M-pages
		   unsigned-byte-p
		   signed-byte-p)))

(defrule translation-governing-addresses-for-pml4-table-and-ia32e-la-to-pa-pml4-table-pairwise-disjoint
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr-2 pml4-base-addr-2 wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)
		(pairwise-disjoint-p
		 (append
		  (translation-governing-addresses-for-pml4-table
		   lin-addr-2 pml4-base-addr-2 x86)
		  (translation-governing-addresses-for-pml4-table
		   lin-addr-1 pml4-base-addr-1 x86))))

	   (equal
	    (translation-governing-addresses-for-pml4-table
	     lin-addr-1 pml4-base-addr-1
	     (mv-nth 2
		     (ia32e-la-to-pa-pml4-table
		      lin-addr-2 pml4-base-addr-2
		      wp-2 smep-2 nxe-2 r-w-x-2 cpl-2 x86)))
	    (translation-governing-addresses-for-pml4-table
	     lin-addr-1 pml4-base-addr-1 x86)))

  :in-theory (e/d
	      ()
	      (ia32e-la-to-pa-pml4-table-entry-validp
	       addr-range-1
	       mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
	       mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
	       member-p-cons
	       disjoint-p-cons
	       not
	       unsigned-byte-p
	       signed-byte-p)))

;; 1G pages:

(defrule translation-governing-addresses-for-pml4-table-and-ia32e-la-to-pa-pml4-table-same-addr-1G-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)
		(pairwise-disjoint-p
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))

		(physical-address-p pml4-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 pml4-base-addr) 0)
		(x86p x86))
	   (equal
	    (translation-governing-addresses-for-pml4-table
	     lin-addr pml4-base-addr
	     (mv-nth 2
		     (ia32e-la-to-pa-pml4-table
		      lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)))
	    (translation-governing-addresses-for-pml4-table
	     lin-addr pml4-base-addr x86)))
  :use ((:instance pml4-table-entry-validp-to-page-dir-ptr-entry-validp)
	(:instance page-size-from-re-reading-page-dir-ptr-table-entry-given-pml4-entry-validp-1G-pages))
  :in-theory (e/d
	      (logtail-12-of-reading-pml4-entry-from-state-after-page-dir-ptr-table-given-pml4-table-validp-1G-pages)
	      (pml4-table-entry-validp-to-page-dir-ptr-entry-validp
	       ia32e-la-to-pa-pml4-table-entry-validp
	       translation-governing-addresses-for-page-dir-ptr-table
	       mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1g-pages
	       mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
	       addr-range-1
	       member-p-cons
	       disjoint-p-cons
	       not
	       unsigned-byte-p
	       signed-byte-p)))

(defrule translation-governing-addresses-for-pml4-table-and-ia32e-la-to-pa-pml4-table-same-addr-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)

		(pairwise-disjoint-p
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))

		(physical-address-p pml4-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 pml4-base-addr) 0)
		(x86p x86))
	   (equal
	    (translation-governing-addresses-for-pml4-table
	     lin-addr pml4-base-addr
	     (mv-nth 2
		     (ia32e-la-to-pa-pml4-table
		      lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)))
	    (translation-governing-addresses-for-pml4-table
	     lin-addr pml4-base-addr x86)))
  :use ((:instance pml4-table-entry-validp-to-page-dir-ptr-entry-validp)
	(:instance page-size-from-re-reading-page-dir-ptr-table-entry-given-pml4-entry-validp-2M-pages)
	(:instance page-size-from-reading-page-directory-entry-from-state-after-page-dir-ptr-table-given-pml4-entry-validp-2M-pages))
  :in-theory (e/d
	      (logtail-12-of-reading-page-dir-ptr-table-entry-from-state-after-page-dir-ptr-table-given-pml4-table-validp-2M-pages)
	      (pml4-table-entry-validp-to-page-dir-ptr-entry-validp
	       ia32e-la-to-pa-pml4-table-entry-validp
	       translation-governing-addresses-for-page-dir-ptr-table
	       mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1g-pages
	       mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
	       addr-range-1
	       member-p-cons
	       disjoint-p-cons
	       not
	       unsigned-byte-p
	       signed-byte-p)))

(defrule translation-governing-addresses-for-pml4-table-and-ia32e-la-to-pa-pml4-table-same-addr-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-pml4-table-entry-validp
		 lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86)
		(equal pml4-entry-addr
		       (pml4-table-entry-addr lin-addr pml4-base-addr))
		(equal pml4-entry (rm-low-64 pml4-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))


		(pairwise-disjoint-p
		 (translation-governing-addresses-for-pml4-table
		  lin-addr pml4-base-addr x86))

		(physical-address-p pml4-base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 pml4-base-addr) 0)
		(x86p x86))
	   (equal
	    (translation-governing-addresses-for-pml4-table
	     lin-addr pml4-base-addr
	     (mv-nth 2
		     (ia32e-la-to-pa-pml4-table
		      lin-addr pml4-base-addr
		      wp smep nxe r-w-x cpl x86)))
	    (translation-governing-addresses-for-pml4-table
	     lin-addr pml4-base-addr x86)))
  :use ((:instance pml4-table-entry-validp-to-page-dir-ptr-entry-validp)
	(:instance page-size-from-re-reading-page-dir-ptr-table-entry-given-pml4-entry-validp-4K-pages)
	(:instance page-size-from-reading-page-directory-entry-from-state-after-page-dir-ptr-table-given-pml4-entry-validp-4K-pages))
  :in-theory (e/d
	      (logtail-12-of-reading-page-dir-ptr-table-entry-from-state-after-page-dir-ptr-table-given-pml4-table-validp-4K-pages)
	      (pml4-table-entry-validp-to-page-dir-ptr-entry-validp
	       ia32e-la-to-pa-pml4-table-entry-validp
	       translation-governing-addresses-for-page-dir-ptr-table
	       mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1g-pages
	       mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
	       addr-range-1
	       member-p-cons
	       disjoint-p-cons
	       not
	       unsigned-byte-p
	       signed-byte-p)))

(in-theory (e/d () (ia32e-la-to-pa-pml4-table-entry-validp)))

;; ======================================================================

;; ia32e-la-to-pa:

;; ......................................................................
;; Rules about the three return values of ia32e-la-to-pa:
;; ......................................................................

(defrule mv-nth-0-no-error-ia32e-la-to-pa
  :parents (reasoning-about-page-tables)
  (implies (ia32e-la-to-pa-validp lin-addr r-w-x cpl x86)
	   (equal (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl x86))
		  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa) (not force (force))))

(defrule mv-nth-1-no-error-ia32e-la-to-pa
  :parents (reasoning-about-page-tables)
  (implies (and (equal cr0 (n32 (ctri *cr0* x86)))
		(equal cr4 (n21 (ctri *cr4* x86)))
		(equal ia32-efer
		       (n12 (msri *ia32_efer-idx* x86)))
		(equal wp (cr0-slice :cr0-wp cr0))
		(equal smep (cr4-slice :cr4-smep cr4))
		(equal nxe
		       (ia32_efer-slice :ia32_efer-nxe ia32-efer))
		(equal cr3 (ctri *cr3* x86))
		(equal pml4-base-addr
		       (ash (cr3-slice :cr3-pdb cr3) 12)))
	   (equal (mv-nth 1
			  (ia32e-la-to-pa lin-addr r-w-x cpl x86))
		  (mv-nth 1
			  (ia32e-la-to-pa-pml4-table
			   lin-addr pml4-base-addr wp smep nxe
			   r-w-x cpl x86))))

  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa) (not force (force))))

(defrule mv-nth-2-no-error-ia32e-la-to-pa
  :parents (reasoning-about-page-tables)
  (implies (and (equal cr0 (n32 (ctri *cr0* x86)))
		(equal cr4 (n21 (ctri *cr4* x86)))
		(equal ia32-efer
		       (n12 (msri *ia32_efer-idx* x86)))
		(equal wp (cr0-slice :cr0-wp cr0))
		(equal smep (cr4-slice :cr4-smep cr4))
		(equal nxe
		       (ia32_efer-slice :ia32_efer-nxe ia32-efer))
		(equal cr3 (ctri *cr3* x86))
		(equal pml4-base-addr
		       (ash (cr3-slice :cr3-pdb cr3) 12)))
	   (equal (mv-nth
		   2
		   (ia32e-la-to-pa lin-addr r-w-x cpl x86))
		  (mv-nth
		   2
		   (ia32e-la-to-pa-pml4-table
		    lin-addr pml4-base-addr wp smep nxe r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa)
		  (not)))

(defrule mv-nth-0-no-error-ia32e-la-to-pa-with-disjoint-!memi
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-validp lin-addr r-w-x cpl x86)
		(pairwise-disjoint-p-aux
		 (addr-range 1 addr)
		 (translation-governing-addresses lin-addr x86)))
	   (equal (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl (xw :mem addr val x86)))
		  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa)
		  (not
		   addr-range-1
		   unsigned-byte-p
		   signed-byte-p)))

(defrule mv-nth-0-no-error-ia32e-la-to-pa-with-disjoint-wm-low-64
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-validp lin-addr r-w-x cpl x86)
		(pairwise-disjoint-p-aux
		 (addr-range 8 addr)
		 (translation-governing-addresses lin-addr x86))
		(integerp addr))
	   (equal (mv-nth 0 (ia32e-la-to-pa lin-addr r-w-x cpl (wm-low-64 addr val x86)))
		  nil))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa)
		  (not
		   addr-range-1
		   unsigned-byte-p
		   signed-byte-p)))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-with-disjoint-!memi
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-validp lin-addr r-w-x cpl x86)
		(pairwise-disjoint-p-aux
		 (addr-range 1 addr)
		 (translation-governing-addresses lin-addr x86))
		(integerp addr))
	   (equal (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl (xw :mem addr val x86)))
		  (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa)
		  (mv-nth-1-no-error-ia32e-la-to-pa-pml4-table
		   not
		   addr-range-1
		   unsigned-byte-p
		   signed-byte-p)))

(defrule mv-nth-1-no-error-ia32e-la-to-pa-with-disjoint-wm-low-64
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-validp lin-addr r-w-x cpl x86)
		(pairwise-disjoint-p-aux
		 (addr-range 8 addr)
		 (translation-governing-addresses lin-addr x86))
		(integerp addr))
	   (equal (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl (wm-low-64 addr val x86)))
		  (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x cpl x86))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa)
		  (mv-nth-1-no-error-ia32e-la-to-pa-pml4-table
		   pairwise-disjoint-p-aux
		   not
		   addr-range-1
		   unsigned-byte-p
		   signed-byte-p)))

;; ......................................................................
;; !memi and state after data structure walk WoW theorem:
;; ......................................................................

(defrule disjoint-!memi-mv-nth-2-no-error-ia32e-la-to-pa
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-validp lin-addr r-w-x cpl x86)
		(pairwise-disjoint-p-aux
		 (addr-range 1 addr)
		 (translation-governing-addresses lin-addr x86))
		(integerp addr))
	   (equal
	    (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x cpl (xw :mem addr val x86)))
	    (xw :mem addr val (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa)
		  (not
		   addr-range-1
		   mv-nth-2-no-error-ia32e-la-to-pa-pml4-table)))

;; ......................................................................
;; Reading addresses disjoint from pml4-table-entry-addr after
;; walking all the page tables:
;; ......................................................................

(defrule disjoint-memi-read-mv-nth-2-no-error-ia32e-la-to-pa
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-validp lin-addr r-w-x cpl x86)
		(pairwise-disjoint-p-aux
		 (addr-range 1 addr)
		 (translation-governing-addresses lin-addr x86)))
	   (equal
	    (xr :mem addr (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))
	    (xr :mem addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa)
		  (not
		   addr-range-1
		   mv-nth-2-no-error-ia32e-la-to-pa-pml4-table)))

(defrule disjoint-rm-low-64-read-mv-nth-2-no-error-ia32e-la-to-pa
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-validp lin-addr r-w-x cpl x86)
		(pairwise-disjoint-p-aux
		 (addr-range 8 addr)
		 (translation-governing-addresses lin-addr x86))
		(integerp addr))
	   (equal
	    (rm-low-64 addr (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))
	    (rm-low-64 addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa)
		  (not
		   mv-nth-2-no-error-ia32e-la-to-pa-pml4-table)))

(defrule disjoint-rm-low-32-read-mv-nth-2-no-error-ia32e-la-to-pa
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-validp lin-addr r-w-x cpl x86)
		(pairwise-disjoint-p-aux
		 (addr-range 4 addr)
		 (translation-governing-addresses lin-addr x86))
		(integerp addr))
	   (equal
	    (rm-low-32 addr (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x cpl x86)))
	    (rm-low-32 addr x86)))
  :do-not '(preprocess)
  :in-theory (e/d (ia32e-la-to-pa)
		  (not
		   mv-nth-2-no-error-ia32e-la-to-pa-pml4-table)))

;; ......................................................................
;; Theorems that state that the validity of the paging data structure
;; entries is preserved when writes are done to disjoint addresses or
;; :a/:d are set:
;; ......................................................................

(defrule entry-with-disjoint-!memi-still-valid-ia32e-la-to-pa
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-validp lin-addr r-w-x cpl x86)
		(pairwise-disjoint-p-aux
		 (addr-range 1 addr)
		 (translation-governing-addresses lin-addr x86)))
	   (ia32e-la-to-pa-validp
	    lin-addr r-w-x cpl (xw :mem addr val x86)))
  :in-theory (e/d (ia32e-la-to-pa)
		  (not
		   addr-range-1
		   unsigned-byte-p
		   signed-byte-p)))

(defrule entry-with-disjoint-wm-low-64-still-valid-ia32e-la-to-pa
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-validp lin-addr r-w-x cpl x86)
		(pairwise-disjoint-p-aux
		 (addr-range 8 addr)
		 (translation-governing-addresses lin-addr x86))
		(integerp addr))
	   (ia32e-la-to-pa-validp
	    lin-addr r-w-x cpl (wm-low-64 addr val x86)))
  :in-theory (e/d (ia32e-la-to-pa)
		  (not
		   addr-range-1
		   unsigned-byte-p
		   signed-byte-p)))

;; ......................................................................
;; Theorems about preservation of validity of paging data structure
;; entries:
;; ......................................................................

;; 1G pages:

(defrule re-read-entry-still-valid-ia32e-la-to-pa-1G-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-validp lin-addr r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-validp lin-addr r-w-x-2 cpl-2 x86)
		;; For ia32e-la-to-pa-pml4-table
		(equal base-addr (ash (cr3-slice :cr3-pdb (ctri *cr3* x86)) 12))
		(equal p-entry-addr
		       (pml4-table-entry-addr lin-addr base-addr))
		(equal entry (rm-low-64 p-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

		(disjoint-p (addr-range 8 p-entry-addr)
			    (addr-range 8 ptr-table-entry-addr))
		(physical-address-p base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 base-addr) 0)
		(x86p x86))
	   (ia32e-la-to-pa-validp lin-addr r-w-x-1 cpl-1
				  (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x-2 cpl-2 x86))))
  :do-not '(preprocess)
  :in-theory (e/d
	      (rm-low-64-and-ia32e-la-to-pa-pml4-table-1G-pages

	       ;; The following theorem causes overflows.
	       ;; rm-low-64-and-page-dir-ptr-table-1G-pages
	       )
	      (mv-nth-2-no-error-ia32e-la-to-pa-pml4-table
	       not
	       mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-1g-pages
	       mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1g-pages
	       acl2::mv-nth-cons-meta
	       unsigned-byte-p
	       signed-byte-p)))

;; 2M pages:

(defrule re-read-entry-still-valid-ia32e-la-to-pa-2M-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-validp lin-addr r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-validp lin-addr r-w-x-2 cpl-2 x86)
		;; For ia32e-la-to-pa-pml4-table
		(equal base-addr (ash (cr3-slice :cr3-pdb (ctri *cr3* x86)) 12))
		(equal p-entry-addr
		       (pml4-table-entry-addr lin-addr base-addr))
		(equal entry (rm-low-64 p-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)

		(pairwise-disjoint-p
		 (list (addr-range 8 p-entry-addr)
		       (addr-range 8 ptr-table-entry-addr)
		       (addr-range 8 page-directory-entry-addr)))
		(physical-address-p base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 base-addr) 0)
		(x86p x86))

	   (ia32e-la-to-pa-validp
	    lin-addr r-w-x-1 cpl-1
	    (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x-2 cpl-2 x86))))
  :do-not '(preprocess)
  :in-theory (e/d ()
		  (mv-nth-2-no-error-ia32e-la-to-pa-pml4-table
		   not
		   mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
		   not
		   acl2::mv-nth-cons-meta
		   unsigned-byte-p
		   signed-byte-p)))

;; 4K pages:

(defrule re-read-entry-still-valid-ia32e-la-to-pa-4K-pages
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-validp lin-addr r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-validp lin-addr r-w-x-2 cpl-2 x86)
		;; For ia32e-la-to-pa-pml4-table
		(equal base-addr (ash (cr3-slice :cr3-pdb (ctri *cr3* x86)) 12))
		(equal p-entry-addr
		       (pml4-table-entry-addr lin-addr base-addr))
		(equal entry (rm-low-64 p-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
		;; For ia32e-la-to-pa-page-table:
		(equal page-table-base-addr
		       (ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
		(equal page-table-entry-addr
		       (page-table-entry-addr lin-addr page-table-base-addr))

		(pairwise-disjoint-p
		 (list (addr-range 8 p-entry-addr)
		       (addr-range 8 ptr-table-entry-addr)
		       (addr-range 8 page-directory-entry-addr)
		       (addr-range 8 page-table-entry-addr)))

		(physical-address-p base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 base-addr) 0)
		(x86p x86))

	   (ia32e-la-to-pa-validp
	    lin-addr r-w-x-1 cpl-1
	    (mv-nth
	     2
	     (ia32e-la-to-pa lin-addr r-w-x-2 cpl-2 x86))))
  :do-not '(preprocess)
  :in-theory (e/d ()
		  (mv-nth-2-no-error-ia32e-la-to-pa-pml4-table
		   not
		   mv-nth-1-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
		   mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
		   not
		   acl2::mv-nth-cons-meta
		   unsigned-byte-p
		   signed-byte-p)))

;; ......................................................................
;; Two walks theorem --- same addresses:
;; ......................................................................

;; 1G pages:

(defrule two-page-table-walks-ia32e-la-to-pa-1G-pages-same-addresses
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-validp lin-addr r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-validp lin-addr r-w-x-2 cpl-2 x86)
		;; For ia32e-la-to-pa-pml4-table
		(equal base-addr (ash (cr3-slice :cr3-pdb (ctri *cr3* x86)) 12))
		(equal p-entry-addr
		       (pml4-table-entry-addr lin-addr base-addr))
		(equal entry (rm-low-64 p-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

		(pairwise-disjoint-p
		 (translation-governing-addresses lin-addr x86))
		(physical-address-p base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 base-addr) 0)
		(x86p x86))
	   (equal
	    (mv-nth 1
		    (ia32e-la-to-pa
		     lin-addr r-w-x-1 cpl-1
		     (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x-2 cpl-2 x86))))
	    (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x-1 cpl-1 x86))))
  :do-not '(preprocess)
  :in-theory (e/d
	      ()
	      (mv-nth-2-no-error-ia32e-la-to-pa-pml4-table
	       member-p-cons
	       disjoint-p-cons
	       not
	       unsigned-byte-p
	       signed-byte-p)))

(defrule two-page-table-walks-ia32e-la-to-pa-1G-pages-same-entry-different-addrs
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-validp lin-addr-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-validp lin-addr-2 r-w-x-2 cpl-2 x86)
		;; For ia32e-la-to-pa-pml4-table
		(equal base-addr (ash (cr3-slice :cr3-pdb (ctri *cr3* x86)) 12))
		(equal p-entry-addr
		       (pml4-table-entry-addr lin-addr-1 base-addr))
		(equal entry (rm-low-64 p-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr-1 ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 1)

		(pairwise-disjoint-p
		 (translation-governing-addresses lin-addr-1 x86))
		;; So that pml4 table entries are the same...
		(equal (part-select lin-addr-1 :low 39 :high 47)
		       (part-select lin-addr-2 :low 39 :high 47))
		;; So that the ptr table entries are the same...
		(equal (part-select lin-addr-1 :low 30 :high 38)
		       (part-select lin-addr-2 :low 30 :high 38))
		;; So that the physical addresses are different...
		(not (equal (part-select lin-addr-1 :low 0 :high 29)
			    (part-select lin-addr-2 :low 0 :high 29)))
		(physical-address-p base-addr)
		(canonical-address-p lin-addr-1)
		(canonical-address-p lin-addr-2)
		(equal (loghead 12 base-addr) 0)
		(x86p x86))
	   (equal
	    (mv-nth 1
		    (ia32e-la-to-pa
		     lin-addr-1 r-w-x-1 cpl-1
		     (mv-nth 2 (ia32e-la-to-pa lin-addr-2 r-w-x-2 cpl-2 x86))))
	    (mv-nth 1 (ia32e-la-to-pa lin-addr-1 r-w-x-1 cpl-1 x86))))
  :do-not '(preprocess)
  :in-theory (e/d
	      ()
	      (mv-nth-2-no-error-ia32e-la-to-pa-pml4-table
	       mv-nth-1-no-error-ia32e-la-to-pa-pml4-table
	       member-p-cons
	       disjoint-p-cons
	       not
	       unsigned-byte-p
	       signed-byte-p)))

;; 2M pages:

(defrule two-page-table-walks-ia32e-la-to-pa-2M-pages-same-addresses
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-validp lin-addr r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-validp lin-addr r-w-x-2 cpl-2 x86)
		;; For ia32e-la-to-pa-pml4-table
		(equal base-addr (ash (cr3-slice :cr3-pdb (ctri *cr3* x86)) 12))
		(equal p-entry-addr
		       (pml4-table-entry-addr lin-addr base-addr))
		(equal entry (rm-low-64 p-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)

		(pairwise-disjoint-p
		 (translation-governing-addresses lin-addr x86))

		(physical-address-p base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 base-addr) 0)
		(x86p x86))
	   (equal
	    (mv-nth
	     1
	     (ia32e-la-to-pa
	      lin-addr r-w-x-1 cpl-1
	      (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x-2 cpl-2 x86))))
	    (mv-nth
	     1
	     (ia32e-la-to-pa lin-addr r-w-x-1 cpl-1 x86))))
  :do-not '(preprocess)
  :in-theory (e/d
	      ()
	      (mv-nth-2-no-error-ia32e-la-to-pa-pml4-table
	       member-p-cons
	       disjoint-p-cons
	       not
	       unsigned-byte-p
	       signed-byte-p)))

(defrule two-page-table-walks-ia32e-la-to-pa-2M-pages-same-entry-different-addrs
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-validp lin-addr-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-validp lin-addr-2 r-w-x-2 cpl-2 x86)
		;; For ia32e-la-to-pa-pml4-table
		(equal base-addr (ash (cr3-slice :cr3-pdb (ctri *cr3* x86)) 12))
		(equal p-entry-addr
		       (pml4-table-entry-addr lin-addr-1 base-addr))
		(equal entry (rm-low-64 p-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr-1 ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr-1 page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 1)

		(pairwise-disjoint-p
		 (list (addr-range 8 p-entry-addr)
		       (addr-range 8 ptr-table-entry-addr)
		       (addr-range 8 page-directory-entry-addr)))
		;; So that pml4 table entries are the same...
		(equal (part-select lin-addr-1 :low 39 :high 47)
		       (part-select lin-addr-2 :low 39 :high 47))
		;; So that the ptr table entries are the same...
		(equal (part-select lin-addr-1 :low 30 :high 38)
		       (part-select lin-addr-2 :low 30 :high 38))
		;; So that the page directory entries are the same...
		(equal (part-select lin-addr-1 :low 21 :high 29)
		       (part-select lin-addr-2 :low 21 :high 29))
		;; So that the physical address is different...
		(not (equal (part-select lin-addr-1 :low 0 :high 20)
			    (part-select lin-addr-2 :low 0 :high 20)))
		(physical-address-p base-addr)
		(canonical-address-p lin-addr-1)
		(canonical-address-p lin-addr-2)
		(equal (loghead 12 base-addr) 0)
		(x86p x86))
	   (equal
	    (mv-nth
	     1
	     (ia32e-la-to-pa
	      lin-addr-1 r-w-x-1 cpl-1
	      (mv-nth 2 (ia32e-la-to-pa lin-addr-2 r-w-x-2 cpl-2 x86))))
	    (mv-nth
	     1
	     (ia32e-la-to-pa lin-addr-1 r-w-x-1 cpl-1 x86))))
  :do-not '(preprocess)
  :in-theory (e/d
	      ()
	      (mv-nth-1-no-error-ia32e-la-to-pa-pml4-table
	       mv-nth-2-no-error-ia32e-la-to-pa-pml4-table
	       member-p-cons
	       disjoint-p-cons
	       not
	       unsigned-byte-p
	       signed-byte-p)))

;; 4K pages:

(defrule two-page-table-walks-ia32e-la-to-pa-4K-pages-same-addresses
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-validp lin-addr r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-validp lin-addr r-w-x-2 cpl-2 x86)
		;; For ia32e-la-to-pa-pml4-table
		(equal base-addr (ash (cr3-slice :cr3-pdb (ctri *cr3* x86)) 12))
		(equal p-entry-addr
		       (pml4-table-entry-addr lin-addr base-addr))
		(equal entry (rm-low-64 p-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
		(pairwise-disjoint-p
		 (translation-governing-addresses lin-addr x86))
		(physical-address-p base-addr)
		(canonical-address-p lin-addr)
		(equal (loghead 12 base-addr) 0)
		(x86p x86))
	   (equal
	    (mv-nth
	     1
	     (ia32e-la-to-pa lin-addr r-w-x-1 cpl-1
			     (mv-nth 2 (ia32e-la-to-pa lin-addr r-w-x-2 cpl-2 x86))))
	    (mv-nth 1 (ia32e-la-to-pa lin-addr r-w-x-1 cpl-1 x86))))
  :in-theory (e/d
	      ()
	      (mv-nth-2-no-error-ia32e-la-to-pa-pml4-table
	       member-p-cons
	       disjoint-p-cons
	       not
	       unsigned-byte-p
	       signed-byte-p)))

(defrule two-page-table-walks-ia32e-la-to-pa-4K-pages-same-entry-different-addrs
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-validp lin-addr-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-validp lin-addr-2 r-w-x-2 cpl-2 x86)
		;; For ia32e-la-to-pa-pml4-table
		(equal base-addr (ash (cr3-slice :cr3-pdb (ctri *cr3* x86)) 12))
		(equal p-entry-addr
		       (pml4-table-entry-addr lin-addr-1 base-addr))
		(equal entry (rm-low-64 p-entry-addr x86))
		;; For ia32e-la-to-pa-page-dir-ptr-table:
		(equal ptr-table-base-addr
		       (ash (ia32e-pml4e-slice :pml4e-pdpt entry) 12))
		(equal ptr-table-entry-addr
		       (page-dir-ptr-table-entry-addr lin-addr-1 ptr-table-base-addr))
		(equal ptr-table-entry (rm-low-64 ptr-table-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps  ptr-table-entry) 0)
		;; For ia32e-la-to-pa-page-directory:
		(equal page-directory-base-addr
		       (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd ptr-table-entry) 12))
		(equal page-directory-entry-addr
		       (page-directory-entry-addr lin-addr-1 page-directory-base-addr))
		(equal page-directory-entry (rm-low-64 page-directory-entry-addr x86))
		(equal (ia32e-page-tables-slice :ps page-directory-entry) 0)
		(pairwise-disjoint-p
		 (translation-governing-addresses lin-addr-1 x86))

		;; So that pml4 table entries are the same...
		(equal (part-select lin-addr-1 :low 39 :high 47)
		       (part-select lin-addr-2 :low 39 :high 47))
		;; So that the ptr table entries are the same...
		(equal (part-select lin-addr-1 :low 30 :high 38)
		       (part-select lin-addr-2 :low 30 :high 38))
		;; So that the page directory entries are the same...
		(equal (part-select lin-addr-1 :low 21 :high 29)
		       (part-select lin-addr-2 :low 21 :high 29))
		;; So that the page table entries are the same...
		(equal (part-select lin-addr-1 :low 12 :high 20)
		       (part-select lin-addr-2 :low 12 :high 20))
		;; So that the physical address is different...
		(not (equal (part-select lin-addr-1 :low 0 :width 12)
			    (part-select lin-addr-2 :low 0 :width 12)))

		(physical-address-p base-addr)
		(canonical-address-p lin-addr-1)
		(canonical-address-p lin-addr-2)
		(equal (loghead 12 base-addr) 0)
		(x86p x86))
	   (equal
	    (mv-nth
	     1
	     (ia32e-la-to-pa lin-addr-1 r-w-x-1 cpl-1
			     (mv-nth 2 (ia32e-la-to-pa lin-addr-2 r-w-x-2 cpl-2 x86))))
	    (mv-nth 1 (ia32e-la-to-pa lin-addr-1 r-w-x-1 cpl-1 x86))))
  :in-theory (e/d
	      ()
	      (mv-nth-2-no-error-ia32e-la-to-pa-pml4-table
	       mv-nth-1-no-error-ia32e-la-to-pa-pml4-table
	       member-p-cons
	       disjoint-p-cons
	       not
	       unsigned-byte-p
	       signed-byte-p)))

;; ......................................................................
;; Two walks theorem --- different entries
;; ......................................................................

(defrule two-page-table-walks-ia32e-la-to-pa-different-entries
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-validp lin-addr-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-validp lin-addr-2 r-w-x-2 cpl-2 x86)

		(pairwise-disjoint-p
		 (append
		  (translation-governing-addresses lin-addr-2 x86)
		  (translation-governing-addresses lin-addr-1 x86)))

		(canonical-address-p lin-addr-1)
		(canonical-address-p lin-addr-2)
		(x86p x86))
	   (equal (mv-nth 1
			  (ia32e-la-to-pa lin-addr-1 r-w-x-1 cpl-1
					  (mv-nth 2 (ia32e-la-to-pa
						     lin-addr-2 r-w-x-2 cpl-2 x86))))
		  (mv-nth 1
			  (ia32e-la-to-pa lin-addr-1 r-w-x-1 cpl-1 x86))))
  :do-not '(preprocess)
  :in-theory (e/d ()
		  (ia32e-la-to-pa-pml4-table-entry-validp
		   translation-governing-addresses-for-pml4-table
		   page-dir-ptr-entry-validp-to-page-directory-entry-validp
		   mv-nth-1-no-error-ia32e-la-to-pa-pml4-table
		   mv-nth-2-no-error-ia32e-la-to-pa-pml4-table
		   reading-entry-with-accessed-bit-set-ia32e-la-to-pa-pml4-table-4k-pages
		   addr-range
		   member-p-cons
		   disjoint-p-cons
		   not
		   unsigned-byte-p
		   signed-byte-p)))

;; ......................................................................
;; Validity of paging structure entries are preserved when the
;; translation-governing addresses are disjoint:
;; ......................................................................

(defrule validity-preserved-same-x86-state-disjoint-addresses-top-level-thm
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-validp lin-addr-1 r-w-x-1 cpl-1 x86)
		(ia32e-la-to-pa-validp lin-addr-2 r-w-x-2 cpl-2 x86)

		(pairwise-disjoint-p
		 (append
		  (translation-governing-addresses lin-addr-2 x86)
		  (translation-governing-addresses lin-addr-1 x86)))

		(canonical-address-p lin-addr-1)
		(canonical-address-p lin-addr-2)
		(x86p x86))

	   (ia32e-la-to-pa-validp lin-addr-1 r-w-x-1 cpl-1
				  (mv-nth 2 (ia32e-la-to-pa
					     lin-addr-2 r-w-x-2 cpl-2 x86))))
  :in-theory (e/d
	      ()
	      (mv-nth-2-no-error-ia32e-la-to-pa-pml4-table
	       mv-nth-1-no-error-ia32e-la-to-pa-pml4-table
	       translation-governing-addresses-for-pml4-table
	       member-p-cons
	       disjoint-p-cons
	       not
	       unsigned-byte-p
	       signed-byte-p)))

;; ......................................................................
;; Translation-Governing-Addresses and ia32e-la-to-pa:
;; ......................................................................

(defrule translation-governing-addresses-and-ia32e-la-to-pa-pairwise-disjoint
  :parents (reasoning-about-page-tables)
  (implies (and (ia32e-la-to-pa-validp lin-addr-2 r-w-x-2 cpl-2 x86)
		(pairwise-disjoint-p
		 (append
		  (translation-governing-addresses lin-addr-2 x86)
		  (translation-governing-addresses lin-addr-1 x86))))

	   (equal
	    (translation-governing-addresses
	     lin-addr-1
	     (mv-nth 2
		     (ia32e-la-to-pa
		      lin-addr-2 r-w-x-2 cpl-2 x86)))
	    (translation-governing-addresses lin-addr-1 x86)))

  :in-theory (e/d
	      ()
	      (ia32e-la-to-pa-pml4-table-entry-validp
	       addr-range-1
	       mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-1G-pages
	       mv-nth-2-no-error-ia32e-la-to-pa-page-dir-ptr-table-4k-or-2m-pages
	       member-p-cons
	       disjoint-p-cons
	       not
	       unsigned-byte-p
	       signed-byte-p)))

;; ======================================================================
