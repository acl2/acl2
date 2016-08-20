;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "top" :ttags :all)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (include-book "centaur/gl/gl" :dir :system))

(local (in-theory (e/d () (unsigned-byte-p signed-byte-p))))

;; ======================================================================

(def-gl-export accessed-bit-set-accessed-bit-identity
  :hyp (and (equal (accessed-bit e) 1)
	    (unsigned-byte-p 64 e))
  :concl (equal (set-accessed-bit e) e)
  :g-bindings
  (gl::auto-bindings (:nat e 64)))

(def-gl-export dirty-bit-set-dirty-bit-identity
  :hyp (and (equal (dirty-bit e) 1)
	    (unsigned-byte-p 64 e))
  :concl (equal (set-dirty-bit e) e)
  :g-bindings
  (gl::auto-bindings (:nat e 64)))

(defthmd wm-low-32-and-rm-low-32-writing-the-read-simple
  (implies (x86p x86)
	   (equal (wm-low-32 addr (rm-low-32 addr x86) x86)
		  x86))
  :hints (("Goal" :in-theory (e/d* (wm-low-32
				    rm-low-32
				    xw-xr
				    unsigned-byte-p)
				   ()))))

(defthmd wm-low-32-and-rm-low-32-writing-the-read
  (implies (and (equal (rm-low-32 addr x86-2)
		       (rm-low-32 addr x86-1))
		(x86p x86-1)
		(x86p x86-2))
	   (equal (wm-low-32 addr (rm-low-32 addr x86-1) x86-2)
		  x86-2))
  :hints (("Goal" :in-theory (e/d* (wm-low-32-and-rm-low-32-writing-the-read-simple)
				   ()))))

(defthmd wm-low-64-and-rm-low-64-writing-the-read-simple
  (implies (x86p x86)
	   (equal (wm-low-64 addr (rm-low-64 addr x86) x86)
		  x86))
  :hints (("Goal" :in-theory (e/d* (wm-low-64
				    rm-low-64
				    wm-low-32-and-rm-low-32-writing-the-read)
				   ()))))

(defthmd wm-low-64-and-rm-low-64-writing-the-read
  (implies (and (equal (rm-low-64 addr x86-2)
		       (rm-low-64 addr x86-1))
		(x86p x86-1)
		(x86p x86-2))
	   (equal (wm-low-64 addr (rm-low-64 addr x86-1) x86-2)
		  x86-2))
  :hints (("Goal" :in-theory (e/d* (wm-low-64-and-rm-low-64-writing-the-read-simple)
				   ()))))

;; ======================================================================

;; xlate-governing-qword-addresses are similar to
;; translation-governing-addresses, except that they output quadword
;; addresses of the paging entries instead of byte addresses.

(define xlate-governing-qword-addresses-for-page-table
  ((lin-addr             :type (signed-byte   #.*max-linear-address-size*))
   (page-table-base-addr :type (unsigned-byte #.*physical-address-size*))
   (x86))
  :guard (and (not (programmer-level-mode x86))
	      (canonical-address-p lin-addr)
	      (equal (loghead 12 page-table-base-addr) 0))
  :ignore-ok t

  (b* ((page-table-entry-addr
	(page-table-entry-addr lin-addr page-table-base-addr))
       (page-table-entry
	(rm-low-64 page-table-entry-addr x86)))
    ;; 4K pages
    (list page-table-entry-addr))

  ///

  (defthm xlate-governing-qword-and-byte-addresses-for-page-table
    (equal (open-qword-paddr-list
	    (xlate-governing-qword-addresses-for-page-table
	     lin-addr base-addr x86))
	   (translation-governing-addresses-for-page-table
	    lin-addr base-addr x86))
    :hints (("Goal" :in-theory (e/d* (translation-governing-addresses-for-page-table)
				     ())))))

(define xlate-governing-qword-addresses-for-page-directory
  ((lin-addr                 :type (signed-byte   #.*max-linear-address-size*))
   (page-directory-base-addr :type (unsigned-byte #.*physical-address-size*))
   (x86))
  :guard (and (not (programmer-level-mode x86))
	      (canonical-address-p lin-addr)
	      (equal (loghead 12 page-directory-base-addr) 0))
  :guard-hints (("Goal" :in-theory (e/d* (canonical-address-p)
					 (xlate-governing-qword-addresses-for-page-table
					  unsigned-byte-p
					  signed-byte-p
					  acl2::commutativity-of-logior))))

  (b* (
       ;; 2M pages:
       (page-directory-entry-addr
	(page-directory-entry-addr lin-addr page-directory-base-addr))
       (page-directory-entry (rm-low-64 page-directory-entry-addr x86))

       (pde-ps? (equal (page-size page-directory-entry) 1))
       ((when pde-ps?)
	(list page-directory-entry-addr))

       ;; 4K pages:
       (page-table-base-addr
	(ash (ia32e-pde-pg-table-slice :pde-pt page-directory-entry) 12))
       (page-table-address
	(xlate-governing-qword-addresses-for-page-table
	 lin-addr page-table-base-addr x86)))

    (cons page-directory-entry-addr page-table-address))

  ///

  (defthm xlate-governing-qword-and-byte-addresses-for-page-directory
    (equal (open-qword-paddr-list
	    (xlate-governing-qword-addresses-for-page-directory
	     lin-addr base-addr x86))
	   (translation-governing-addresses-for-page-directory
	    lin-addr base-addr x86))
    :hints (("Goal" :in-theory (e/d* (translation-governing-addresses-for-page-directory)
				     ())))))

(define xlate-governing-qword-addresses-for-page-dir-ptr-table
  ((lin-addr                 :type (signed-byte   #.*max-linear-address-size*))
   (ptr-table-base-addr :type (unsigned-byte #.*physical-address-size*))
   (x86))
  :guard (and (not (programmer-level-mode x86))
	      (canonical-address-p lin-addr)
	      (equal (loghead 12 ptr-table-base-addr) 0))
  :guard-hints (("Goal" :in-theory (e/d* (canonical-address-p)
					 (xlate-governing-qword-addresses-for-page-directory
					  unsigned-byte-p
					  signed-byte-p
					  acl2::commutativity-of-logior))))

  (b* ((page-dir-ptr-table-entry-addr
	(page-dir-ptr-table-entry-addr lin-addr ptr-table-base-addr))
       (page-dir-ptr-table-entry (rm-low-64 page-dir-ptr-table-entry-addr x86))

       (pdpte-ps? (equal (page-size page-dir-ptr-table-entry) 1))

       ;; 1G pages:
       ((when pdpte-ps?)
	(list page-dir-ptr-table-entry-addr))

       ;; 2M or 4K pages:

       (page-directory-base-addr (ash (ia32e-pdpte-pg-dir-slice :pdpte-pd page-dir-ptr-table-entry) 12))
       (page-directory-addresses
	(xlate-governing-qword-addresses-for-page-directory
	 lin-addr page-directory-base-addr x86)))

    (cons page-dir-ptr-table-entry-addr page-directory-addresses))

  ///

  (defthm xlate-governing-qword-and-byte-addresses-for-page-dir-ptr-table
    (equal (open-qword-paddr-list
	    (xlate-governing-qword-addresses-for-page-dir-ptr-table
	     lin-addr base-addr x86))
	   (translation-governing-addresses-for-page-dir-ptr-table
	    lin-addr base-addr x86))
    :hints (("Goal" :in-theory (e/d* (translation-governing-addresses-for-page-dir-ptr-table)
				     ())))))

(define xlate-governing-qword-addresses-for-pml4-table
  ((lin-addr       :type (signed-byte   #.*max-linear-address-size*))
   (pml4-base-addr :type (unsigned-byte #.*physical-address-size*))
   (x86))

  :guard (and (not (programmer-level-mode x86))
	      (canonical-address-p lin-addr)
	      (equal (loghead 12 pml4-base-addr) 0))
  :guard-hints (("Goal" :in-theory (e/d* (canonical-address-p)
					 (xlate-governing-qword-addresses-for-page-dir-ptr-table
					  unsigned-byte-p
					  signed-byte-p
					  acl2::commutativity-of-logior))))

  (b* ((pml4-entry-addr
	(pml4-table-entry-addr lin-addr pml4-base-addr))
       (pml4-entry (rm-low-64 pml4-entry-addr x86))
       (pml4te-ps? (equal (page-size pml4-entry) 1))

       ((when pml4te-ps?) (list pml4-entry-addr))

       ;; Page Directory Pointer Table:
       (ptr-table-base-addr
	(ash (ia32e-pml4e-slice :pml4e-pdpt pml4-entry) 12))

       (ptr-table-addresses
	(xlate-governing-qword-addresses-for-page-dir-ptr-table
	 lin-addr ptr-table-base-addr x86)))

    (cons pml4-entry-addr ptr-table-addresses))

  ///

  (defthm xlate-governing-qword-and-byte-addresses-for-pml4-table
    (equal (open-qword-paddr-list
	    (xlate-governing-qword-addresses-for-pml4-table
	     lin-addr base-addr x86))
	   (translation-governing-addresses-for-pml4-table
	    lin-addr base-addr x86))
    :hints (("Goal" :in-theory (e/d* (translation-governing-addresses-for-pml4-table)
				     ())))))

(define xlate-governing-qword-addresses
  ((lin-addr :type (signed-byte   #.*max-linear-address-size*)
	     "Canonical linear address to be mapped to a physical address")
   (x86 "x86 state"))


  :long "<p>@('xlate-governing-qword-addresses') returns a
  @('true-listp') of qword physical addresses that govern the
  translation of a linear address @('lin-addr') to its corresponding
  physical address @('p-addr').  Addresses that can be a part of the
  output (depending on the page configurations, i.e., 4K, 2M, or 1G
  pages) include:</p>

<ol>
<li>The qword address of the relevant PML4 entry</li>

<li>The qword address of the relevant PDPT entry</li>

<li>The qword address of the relevant PD entry</li>

<li>The qword addresses of the relevant PT entry</li>

</ol>

<p>The following rule shows the relationship between @(see
translation-governing-addresses) and
@('xlate-governing-qword-addresses'):</p>

@(def xlate-governing-qword-and-byte-addresses)"

  :guard (not (xr :programmer-level-mode 0 x86))
  :guard-hints (("Goal" :in-theory (e/d* (canonical-address-p)
					 (xlate-governing-qword-addresses-for-pml4-table
					  unsigned-byte-p
					  signed-byte-p
					  acl2::commutativity-of-logior))))

  (if (mbt (not (programmer-level-mode x86)))
      (b* ((cr3       (ctri *cr3* x86))
	   ;; PML4 Table:
	   (pml4-base-addr (ash (cr3-slice :cr3-pdb cr3) 12)))

	(xlate-governing-qword-addresses-for-pml4-table
	 lin-addr pml4-base-addr x86))
    nil)

  ///

  (defthm xlate-governing-qword-and-byte-addresses
    (equal (open-qword-paddr-list
	    (xlate-governing-qword-addresses lin-addr x86))
	   (translation-governing-addresses lin-addr x86))
    :hints (("Goal" :in-theory (e/d* (translation-governing-addresses)
				     ())))))

(define all-xlate-governing-qword-addresses
  ((l-addrs canonical-address-listp)
   x86)
  :guard (not (xr :programmer-level-mode 0 x86))
  :enabled t
  (if (endp l-addrs)
      nil
    (append (xlate-governing-qword-addresses (car l-addrs) x86)
	    (all-xlate-governing-qword-addresses (cdr l-addrs)  x86)))
  ///

  (defthm all-xlate-governing-qword-and-byte-addresses
    (equal (open-qword-paddr-list
	    (all-xlate-governing-qword-addresses l-addrs x86))
	   (all-translation-governing-addresses l-addrs x86))
    :hints (("Goal" :in-theory (e/d* (all-translation-governing-addresses)
				     ())))))

;; ======================================================================

(define update-a/d-bits (p-addrs
			 (r-w-x  :type (member :r :w :x))
			 x86)
  ;; We expect p-addrs to be members of
  ;; xlate-governing-qword-addresses addresses of some linear address
  ;; on whose behalf a page walk is being done.

  ;; Don't use anything other than the output of
  ;; xlate-governing-qword-addresses* functions as input for p-addrs.
  :guard (and (not (programmer-level-mode x86))
	      (mult-8-qword-paddr-listp p-addrs))
  :enabled t
  (if (endp p-addrs)
      (mv nil x86)
    (b* ((p-addr (car p-addrs))
	 ((when (not (physical-address-p (+ 7 p-addr))))
	  (mv t x86))
	 (entry (rm-low-64 p-addr x86))
	 (new-entry (set-accessed-bit entry))
	 (new-entry
	  (if (and (equal (len p-addrs) 1)
		   (equal r-w-x :w))
	      ;; If the entry maps a page and translation is occurring
	      ;; on behalf of a write, set the dirty bit too.
	      (set-dirty-bit new-entry)
	    new-entry))
	 (x86 (wm-low-64 p-addr new-entry x86)))
      (update-a/d-bits (cdr p-addrs) r-w-x x86)))

  ///

  (defthm x86p-mv-nth-1-update-a/d-bits
    (implies (and (x86p x86)
		  (physical-address-listp p-addrs))
	     (x86p (mv-nth 1 (update-a/d-bits p-addrs r-w-x x86))))))

(defthm memi-from-update-a/d-bits-disjoint
  (implies (and (disjoint-p (list index)
			    (open-qword-paddr-list p-addrs))
		(mult-8-qword-paddr-listp p-addrs))
	   (equal (xr :mem index (mv-nth 1 (update-a/d-bits p-addrs r-w-x x86)))
		  (xr :mem index x86))))

(defthm rm-low-64-from-update-a/d-bits-disjoint
  (implies (and (disjoint-p (addr-range 8 index)
			    (open-qword-paddr-list p-addrs))
		(mult-8-qword-paddr-listp p-addrs)
		(integerp index))
	   (equal (rm-low-64 index (mv-nth 1 (update-a/d-bits p-addrs r-w-x x86)))
		  (rm-low-64 index x86))))

(defthm !memi-from-update-a/d-bits-disjoint-commute
  (implies (disjoint-p (list index)
		       (open-qword-paddr-list p-addrs))
	   (equal (xw :mem index val (mv-nth 1 (update-a/d-bits p-addrs r-w-x x86)))
		  (mv-nth 1 (update-a/d-bits p-addrs r-w-x (xw :mem index val x86))))))

(defthm wm-low-64-from-update-a/d-bits-disjoint-commute
  (implies (and (disjoint-p (addr-range 8 index)
			    (open-qword-paddr-list p-addrs))
		(mult-8-qword-paddr-listp p-addrs)
		(integerp index))
	   (equal (wm-low-64 index val (mv-nth 1 (update-a/d-bits p-addrs r-w-x x86)))
		  (mv-nth 1 (update-a/d-bits p-addrs r-w-x (wm-low-64 index val x86))))))

;; ======================================================================

;; Page Table:

(defthm mv-nth-2-ia32e-la-to-pa-page-table-in-terms-of-updates
  (implies (and
	    (xr :page-structure-marking-mode 0 x86)
	    (not
	     (mv-nth 0
		     (ia32e-la-to-pa-page-table
		      lin-addr
		      base-addr u/s-acc r/w-acc x/d-acc
		      wp smep smap ac nxe r-w-x cpl x86)))
	    (x86p x86)
	    (canonical-address-p lin-addr)
	    (physical-address-p base-addr)
	    (equal (loghead 12 base-addr) 0))
	   (equal (mv-nth
		   2
		   (ia32e-la-to-pa-page-table
		    lin-addr base-addr u/s-acc r/w-acc x/d-acc
		    wp smep smap ac nxe r-w-x cpl x86))
		  (mv-nth 1
			  (update-a/d-bits
			   (xlate-governing-qword-addresses-for-page-table
			    lin-addr base-addr x86)
			   r-w-x x86))))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-page-table
				    wm-low-64-and-rm-low-64-writing-the-read
				    xlate-governing-qword-addresses-for-page-table)
				   (bitops::logand-with-negated-bitmask
				    accessed-bit
				    dirty-bit)))))

;; ======================================================================

;; Page Directory:

(local
 (defthmd mv-nth-2-ia32e-la-to-pa-page-directory-in-terms-of-updates-2M-pages
   (implies
    (and
     (equal (page-size
	     (rm-low-64 (page-directory-entry-addr lin-addr base-addr) x86))
	    1)
     (xr :page-structure-marking-mode 0 x86)
     (not
      (mv-nth 0
	      (ia32e-la-to-pa-page-directory
	       lin-addr
	       base-addr u/s-acc r/w-acc x/d-acc
	       wp smep smap ac nxe r-w-x cpl x86)))
     (x86p x86)
     (canonical-address-p lin-addr)
     (physical-address-p base-addr)
     (equal (loghead 12 base-addr) 0))
    (equal (mv-nth
	    2
	    (ia32e-la-to-pa-page-directory
	     lin-addr base-addr u/s-acc r/w-acc x/d-acc
	     wp smep smap ac nxe r-w-x cpl x86))
	   (mv-nth 1
		   (update-a/d-bits
		    (xlate-governing-qword-addresses-for-page-directory
		     lin-addr base-addr x86)
		    r-w-x x86))))
   :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-page-directory
				     wm-low-64-and-rm-low-64-writing-the-read
				     xlate-governing-qword-addresses-for-page-directory)
				    (bitops::logand-with-negated-bitmask
				     accessed-bit
				     dirty-bit))))))

(local
 (defthmd mv-nth-2-ia32e-la-to-pa-page-directory-in-terms-of-updates-4K-pages
   (implies
    (and
     (equal (page-size
	     (rm-low-64 (page-directory-entry-addr lin-addr base-addr)
			x86))
	    0)
     (xr :page-structure-marking-mode 0 x86)
     (not
      (mv-nth 0
	      (ia32e-la-to-pa-page-directory
	       lin-addr
	       base-addr u/s-acc r/w-acc x/d-acc
	       wp smep smap ac nxe r-w-x cpl x86)))
     (x86p x86)
     (canonical-address-p lin-addr)
     (physical-address-p base-addr)
     (equal (loghead 12 base-addr) 0))
    (equal (mv-nth
	    2
	    (ia32e-la-to-pa-page-directory
	     lin-addr base-addr u/s-acc r/w-acc x/d-acc
	     wp smep smap ac nxe r-w-x cpl x86))
	   (mv-nth 1
		   (update-a/d-bits
		    (xlate-governing-qword-addresses-for-page-directory
		     lin-addr base-addr x86)
		    r-w-x x86))))
   :hints (("Goal"
	    :cases ((equal (page-directory-entry-addr lin-addr base-addr)
			   (page-table-entry-addr
			    lin-addr
			    (ash
			     (loghead
			      40
			      (logtail 12
				       (rm-low-64 (page-directory-entry-addr lin-addr base-addr)
						  x86)))
			     12))))
	    :in-theory (e/d* (ia32e-la-to-pa-page-directory
			      wm-low-64-and-rm-low-64-writing-the-read
			      xlate-governing-qword-addresses-for-page-directory
			      xlate-governing-qword-addresses-for-page-table)
			     (bitops::logand-with-negated-bitmask
			      accessed-bit
			      dirty-bit))))))

(defthm mv-nth-2-ia32e-la-to-pa-page-directory-in-terms-of-updates
  (implies
   (and
    (xr :page-structure-marking-mode 0 x86)
    (not
     (mv-nth 0
	     (ia32e-la-to-pa-page-directory
	      lin-addr
	      base-addr u/s-acc r/w-acc x/d-acc
	      wp smep smap ac nxe r-w-x cpl x86)))
    (x86p x86)
    (canonical-address-p lin-addr)
    (physical-address-p base-addr)
    (equal (loghead 12 base-addr) 0))
   (equal (mv-nth
	   2
	   (ia32e-la-to-pa-page-directory
	    lin-addr base-addr u/s-acc r/w-acc x/d-acc
	    wp smep smap ac nxe r-w-x cpl x86))
	  (mv-nth 1
		  (update-a/d-bits
		   (xlate-governing-qword-addresses-for-page-directory
		    lin-addr base-addr x86)
		   r-w-x x86))))
  :hints (("Goal"
	   :cases ((equal (page-size
			   (rm-low-64 (page-directory-entry-addr lin-addr base-addr)
				      x86))
			  0))
	   :in-theory (e/d* (mv-nth-2-ia32e-la-to-pa-page-directory-in-terms-of-updates-4K-pages
			     mv-nth-2-ia32e-la-to-pa-page-directory-in-terms-of-updates-2M-pages)
			    (bitops::logand-with-negated-bitmask
			     accessed-bit
			     dirty-bit)))))

;; ======================================================================

;; Page directory pointer table:

(local
 (defthmd mv-nth-2-ia32e-la-to-pa-page-dir-ptr-table-in-terms-of-updates-1G-pages
   (implies
    (and
     (equal (page-size
	     (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86))
	    1)
     (xr :page-structure-marking-mode 0 x86)
     (not
      (mv-nth 0
	      (ia32e-la-to-pa-page-dir-ptr-table
	       lin-addr
	       base-addr u/s-acc r/w-acc x/d-acc
	       wp smep smap ac nxe r-w-x cpl x86)))
     (x86p x86)
     (canonical-address-p lin-addr)
     (physical-address-p base-addr)
     (equal (loghead 12 base-addr) 0))
    (equal (mv-nth
	    2
	    (ia32e-la-to-pa-page-dir-ptr-table
	     lin-addr base-addr u/s-acc r/w-acc x/d-acc
	     wp smep smap ac nxe r-w-x cpl x86))
	   (mv-nth 1
		   (update-a/d-bits
		    (xlate-governing-qword-addresses-for-page-dir-ptr-table
		     lin-addr base-addr x86)
		    r-w-x x86))))
   :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-page-dir-ptr-table
				     wm-low-64-and-rm-low-64-writing-the-read
				     xlate-governing-qword-addresses-for-page-dir-ptr-table)
				    (bitops::logand-with-negated-bitmask
				     accessed-bit
				     dirty-bit))))))

(local
 (defthmd mv-nth-2-ia32e-la-to-pa-page-dir-ptr-table-in-terms-of-updates-2M-pages
   (implies
    (and
     (equal (page-size
	     (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86))
	    0)
     (equal (page-size
	     (rm-low-64 (page-directory-entry-addr
			 lin-addr
			 (ash
			  (loghead
			   40
			   (logtail
			    12
			    (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr)
				       x86)))
			  12))
			x86))
	    1)
     (xr :page-structure-marking-mode 0 x86)
     (not
      (mv-nth 0
	      (ia32e-la-to-pa-page-dir-ptr-table
	       lin-addr
	       base-addr u/s-acc r/w-acc x/d-acc
	       wp smep smap ac nxe r-w-x cpl x86)))
     (x86p x86)
     (canonical-address-p lin-addr)
     (physical-address-p base-addr)
     (equal (loghead 12 base-addr) 0))
    (equal (mv-nth
	    2
	    (ia32e-la-to-pa-page-dir-ptr-table
	     lin-addr base-addr u/s-acc r/w-acc x/d-acc
	     wp smep smap ac nxe r-w-x cpl x86))
	   (mv-nth 1
		   (update-a/d-bits
		    (xlate-governing-qword-addresses-for-page-dir-ptr-table
		     lin-addr base-addr x86)
		    r-w-x x86))))
   :hints (("Goal"
	    :cases ((equal (page-dir-ptr-table-entry-addr lin-addr base-addr)
			   (page-directory-entry-addr
			    lin-addr
			    (ash
			     (loghead
			      40
			      (logtail
			       12
			       (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr)
					  x86)))
			     12))))
	    :in-theory (e/d* (ia32e-la-to-pa-page-dir-ptr-table
			      wm-low-64-and-rm-low-64-writing-the-read
			      xlate-governing-qword-addresses-for-page-dir-ptr-table
			      xlate-governing-qword-addresses-for-page-directory)
			     (bitops::logand-with-negated-bitmask
			      accessed-bit
			      dirty-bit))))))

(local
 (defthmd mv-nth-2-ia32e-la-to-pa-page-dir-ptr-table-in-terms-of-updates-4K-pages
   (implies
    (and
     (equal (page-size
	     (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86))
	    0)
     (equal (page-size
	     (rm-low-64 (page-directory-entry-addr
			 lin-addr
			 (ash
			  (loghead
			   40
			   (logtail
			    12
			    (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr)
				       x86)))
			  12))
			x86))
	    0)
     (xr :page-structure-marking-mode 0 x86)
     (not
      (mv-nth 0
	      (ia32e-la-to-pa-page-dir-ptr-table
	       lin-addr
	       base-addr u/s-acc r/w-acc x/d-acc
	       wp smep smap ac nxe r-w-x cpl x86)))
     (x86p x86)
     (canonical-address-p lin-addr)
     (physical-address-p base-addr)
     (equal (loghead 12 base-addr) 0))
    (equal (mv-nth
	    2
	    (ia32e-la-to-pa-page-dir-ptr-table
	     lin-addr base-addr u/s-acc r/w-acc x/d-acc
	     wp smep smap ac nxe r-w-x cpl x86))
	   (mv-nth 1
		   (update-a/d-bits
		    (xlate-governing-qword-addresses-for-page-dir-ptr-table
		     lin-addr base-addr x86)
		    r-w-x x86))))
   :hints (("Goal"
	    :cases (
		    ;; PDPT-addr == PD-addr == PT-addr
		    (and
		     (equal (page-dir-ptr-table-entry-addr lin-addr base-addr)
			    (page-directory-entry-addr
			     lin-addr
			     (ash
			      (loghead
			       40
			       (logtail
				12
				(rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr)
					   x86)))
			      12)))
		     (equal
		      (page-directory-entry-addr
		       lin-addr
		       (ash
			(loghead
			 40
			 (logtail
			  12
			  (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr)
				     x86)))
			12))
		      (page-table-entry-addr
		       lin-addr
		       (ash
			(loghead
			 40
			 (logtail
			  12
			  (rm-low-64
			   (page-directory-entry-addr
			    lin-addr
			    (ash
			     (loghead
			      40
			      (logtail
			       12
			       (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr)
					  x86)))
			     12))
			   x86)))
			12))))

		    ;; PDPT-addr == PD-addr != PT-addr
		    (and
		     (equal (page-dir-ptr-table-entry-addr lin-addr base-addr)
			    (page-directory-entry-addr
			     lin-addr
			     (ash
			      (loghead
			       40
			       (logtail
				12
				(rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr)
					   x86)))
			      12)))
		     (not
		      (equal
		       (page-directory-entry-addr
			lin-addr
			(ash
			 (loghead
			  40
			  (logtail
			   12
			   (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr)
				      x86)))
			 12))
		       (page-table-entry-addr
			lin-addr
			(ash
			 (loghead
			  40
			  (logtail
			   12
			   (rm-low-64
			    (page-directory-entry-addr
			     lin-addr
			     (ash
			      (loghead
			       40
			       (logtail
				12
				(rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr)
					   x86)))
			      12))
			    x86)))
			 12)))))

		    ;; PDPT-addr == PT-addr != PD-addr
		    (and
		     (equal (page-dir-ptr-table-entry-addr lin-addr base-addr)
			    (page-table-entry-addr
			     lin-addr
			     (ash
			      (loghead
			       40
			       (logtail
				12
				(rm-low-64
				 (page-directory-entry-addr
				  lin-addr
				  (ash
				   (loghead
				    40
				    (logtail
				     12
				     (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr)
						x86)))
				   12))
				 x86)))
			      12)))
		     (not
		      (equal
		       (page-directory-entry-addr
			lin-addr
			(ash
			 (loghead
			  40
			  (logtail
			   12
			   (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr)
				      x86)))
			 12))
		       (page-table-entry-addr
			lin-addr
			(ash
			 (loghead
			  40
			  (logtail
			   12
			   (rm-low-64
			    (page-directory-entry-addr
			     lin-addr
			     (ash
			      (loghead
			       40
			       (logtail
				12
				(rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr)
					   x86)))
			      12))
			    x86)))
			 12)))))
		    )
	    :in-theory (e/d* (ia32e-la-to-pa-page-dir-ptr-table
			      wm-low-64-and-rm-low-64-writing-the-read
			      xlate-governing-qword-addresses-for-page-dir-ptr-table
			      xlate-governing-qword-addresses-for-page-directory
			      xlate-governing-qword-addresses-for-page-table)
			     (bitops::logand-with-negated-bitmask
			      accessed-bit
			      dirty-bit))))))

(defthm mv-nth-2-ia32e-la-to-pa-page-dir-ptr-table-in-terms-of-updates
  (implies
   (and
    (xr :page-structure-marking-mode 0 x86)
    (not
     (mv-nth 0
	     (ia32e-la-to-pa-page-dir-ptr-table
	      lin-addr
	      base-addr u/s-acc r/w-acc x/d-acc
	      wp smep smap ac nxe r-w-x cpl x86)))
    (x86p x86)
    (canonical-address-p lin-addr)
    (physical-address-p base-addr)
    (equal (loghead 12 base-addr) 0))
   (equal (mv-nth
	   2
	   (ia32e-la-to-pa-page-dir-ptr-table
	    lin-addr base-addr u/s-acc r/w-acc x/d-acc
	    wp smep smap ac nxe r-w-x cpl x86))
	  (mv-nth 1
		  (update-a/d-bits
		   (xlate-governing-qword-addresses-for-page-dir-ptr-table
		    lin-addr base-addr x86)
		   r-w-x x86))))
  :hints (("Goal"
	   :cases (
		   ;; 1G pages
		   (equal (page-size
			   (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86))
			  1)
		   ;; 2M pages
		   (and
		    (equal (page-size
			    (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86))
			   0)
		    (equal (page-size
			    (rm-low-64 (page-directory-entry-addr
					lin-addr
					(ash
					 (loghead
					  40
					  (logtail
					   12
					   (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr)
						      x86)))
					 12))
				       x86))
			   1))
		   ;; 4K pages
		   (and
		    (equal (page-size
			    (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86))
			   0)
		    (equal (page-size
			    (rm-low-64 (page-directory-entry-addr
					lin-addr
					(ash
					 (loghead
					  40
					  (logtail
					   12
					   (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr)
						      x86)))
					 12))
				       x86))
			   0)))
	   :in-theory (e/d* (mv-nth-2-ia32e-la-to-pa-page-dir-ptr-table-in-terms-of-updates-4K-pages
			     mv-nth-2-ia32e-la-to-pa-page-dir-ptr-table-in-terms-of-updates-2M-pages
			     mv-nth-2-ia32e-la-to-pa-page-dir-ptr-table-in-terms-of-updates-1G-pages)
			    (bitops::logand-with-negated-bitmask
			     accessed-bit
			     dirty-bit)))))

;; ======================================================================

;; PML4 Table:

(local
 (defthmd mv-nth-2-ia32e-la-to-pa-pml4-table-in-terms-of-updates-1G-pages
   (implies
    (and
     (equal (page-size
	     (rm-low-64 (page-dir-ptr-table-entry-addr
			 lin-addr
			 (ash
			  (loghead
			   40
			   (logtail 12
				    (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
					       x86)))
			  12))
			x86))
	    1)
     (xr :page-structure-marking-mode 0 x86)
     (not
      (mv-nth 0
	      (ia32e-la-to-pa-pml4-table lin-addr base-addr wp smep
					 smap ac nxe r-w-x cpl x86)))
     (x86p x86)
     (canonical-address-p lin-addr)
     (physical-address-p base-addr)
     (equal (loghead 12 base-addr) 0))
    (equal (mv-nth
	    2
	    (ia32e-la-to-pa-pml4-table lin-addr base-addr wp smep smap
				       ac nxe r-w-x cpl x86))
	   (mv-nth 1
		   (update-a/d-bits
		    (xlate-governing-qword-addresses-for-pml4-table
		     lin-addr base-addr x86)
		    r-w-x x86))))
   :hints (("Goal"
	    :cases ((equal
		     (pml4-table-entry-addr lin-addr base-addr)
		     (page-dir-ptr-table-entry-addr
		      lin-addr
		      (ash
		       (loghead
			40
			(logtail 12
				 (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
					    x86)))
		       12))))
	    :in-theory (e/d* (ia32e-la-to-pa-pml4-table
			      wm-low-64-and-rm-low-64-writing-the-read
			      xlate-governing-qword-addresses-for-pml4-table
			      xlate-governing-qword-addresses-for-page-dir-ptr-table)
			     (bitops::logand-with-negated-bitmask
			      accessed-bit
			      dirty-bit))))))

(local
 (defthmd mv-nth-2-ia32e-la-to-pa-pml4-table-in-terms-of-updates-2M-pages
   (implies
    (and
     (equal (page-size
	     (rm-low-64 (page-dir-ptr-table-entry-addr
			 lin-addr
			 (ash
			  (loghead
			   40
			   (logtail 12
				    (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
					       x86)))
			  12))
			x86))
	    0)
     (equal (page-size
	     (rm-low-64 (page-directory-entry-addr
			 lin-addr
			 (ash
			  (loghead
			   40
			   (logtail
			    12
			    (rm-low-64 (page-dir-ptr-table-entry-addr
					lin-addr
					(ash
					 (loghead
					  40
					  (logtail 12
						   (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
							      x86)))
					 12))
				       x86)))
			  12))
			x86))
	    1)
     (xr :page-structure-marking-mode 0 x86)
     (not
      (mv-nth 0
	      (ia32e-la-to-pa-pml4-table lin-addr base-addr wp smep
					 smap ac nxe r-w-x cpl x86)))
     (x86p x86)
     (canonical-address-p lin-addr)
     (physical-address-p base-addr)
     (equal (loghead 12 base-addr) 0))
    (equal (mv-nth
	    2
	    (ia32e-la-to-pa-pml4-table lin-addr base-addr wp smep smap
				       ac nxe r-w-x cpl x86))
	   (mv-nth 1
		   (update-a/d-bits
		    (xlate-governing-qword-addresses-for-pml4-table
		     lin-addr base-addr x86)
		    r-w-x x86))))
   :hints (("Goal"
	    :cases (
		    ;; PML4TE-addr == PDPTE-addr == PDE-addr
		    (and
		     (equal
		      (pml4-table-entry-addr lin-addr base-addr)
		      (page-dir-ptr-table-entry-addr
		       lin-addr
		       (ash
			(loghead
			 40
			 (logtail 12
				  (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
					     x86)))
			12)))
		     (equal
		      (page-dir-ptr-table-entry-addr
		       lin-addr
		       (ash
			(loghead
			 40
			 (logtail 12
				  (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
					     x86)))
			12))
		      (page-directory-entry-addr
		       lin-addr
		       (ash
			(loghead
			 40
			 (logtail
			  12
			  (rm-low-64 (page-dir-ptr-table-entry-addr
				      lin-addr
				      (ash
				       (loghead
					40
					(logtail 12
						 (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
							    x86)))
				       12))
				     x86)))
			12))))

		    ;; PML4TE-addr == PDPTE-addr != PDE-addr
		    (and
		     (equal
		      (pml4-table-entry-addr lin-addr base-addr)
		      (page-dir-ptr-table-entry-addr
		       lin-addr
		       (ash
			(loghead
			 40
			 (logtail 12
				  (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
					     x86)))
			12)))
		     (not
		      (equal
		       (page-dir-ptr-table-entry-addr
			lin-addr
			(ash
			 (loghead
			  40
			  (logtail 12
				   (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
					      x86)))
			 12))
		       (page-directory-entry-addr
			lin-addr
			(ash
			 (loghead
			  40
			  (logtail
			   12
			   (rm-low-64 (page-dir-ptr-table-entry-addr
				       lin-addr
				       (ash
					(loghead
					 40
					 (logtail 12
						  (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
							     x86)))
					12))
				      x86)))
			 12)))))

		    ;; PML4TE-addr == PDE-addr != PDPTE-addr
		    (and
		     (equal
		      (pml4-table-entry-addr lin-addr base-addr)
		      (page-directory-entry-addr
		       lin-addr
		       (ash
			(loghead
			 40
			 (logtail
			  12
			  (rm-low-64 (page-dir-ptr-table-entry-addr
				      lin-addr
				      (ash
				       (loghead
					40
					(logtail 12
						 (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
							    x86)))
				       12))
				     x86)))
			12)))
		     (not
		      (equal
		       (page-dir-ptr-table-entry-addr
			lin-addr
			(ash
			 (loghead
			  40
			  (logtail 12
				   (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
					      x86)))
			 12))
		       (page-directory-entry-addr
			lin-addr
			(ash
			 (loghead
			  40
			  (logtail
			   12
			   (rm-low-64 (page-dir-ptr-table-entry-addr
				       lin-addr
				       (ash
					(loghead
					 40
					 (logtail 12
						  (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
							     x86)))
					12))
				      x86)))
			 12)))))
		    )
	    :in-theory (e/d* (ia32e-la-to-pa-pml4-table
			      wm-low-64-and-rm-low-64-writing-the-read
			      xlate-governing-qword-addresses-for-pml4-table
			      xlate-governing-qword-addresses-for-page-dir-ptr-table
			      xlate-governing-qword-addresses-for-page-directory)
			     (bitops::logand-with-negated-bitmask
			      accessed-bit
			      dirty-bit))))))

(skip-proofs
 (defthmd mv-nth-2-ia32e-la-to-pa-pml4-table-in-terms-of-updates-4K-pages
   (implies
    (and
     (equal (page-size
	     (rm-low-64 (page-dir-ptr-table-entry-addr
			 lin-addr
			 (ash
			  (loghead
			   40
			   (logtail 12
				    (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
					       x86)))
			  12))
			x86))
	    0)
     (equal (page-size
	     (rm-low-64 (page-directory-entry-addr
			 lin-addr
			 (ash
			  (loghead
			   40
			   (logtail
			    12
			    (rm-low-64 (page-dir-ptr-table-entry-addr
					lin-addr
					(ash
					 (loghead
					  40
					  (logtail 12
						   (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
							      x86)))
					 12))
				       x86)))
			  12))
			x86))
	    0)
     (xr :page-structure-marking-mode 0 x86)
     (not
      (mv-nth 0
	      (ia32e-la-to-pa-pml4-table lin-addr base-addr wp smep
					 smap ac nxe r-w-x cpl x86)))
     (x86p x86)
     (canonical-address-p lin-addr)
     (physical-address-p base-addr)
     (equal (loghead 12 base-addr) 0))
    (equal (mv-nth
	    2
	    (ia32e-la-to-pa-pml4-table lin-addr base-addr wp smep smap
				       ac nxe r-w-x cpl x86))
	   (mv-nth 1
		   (update-a/d-bits
		    (xlate-governing-qword-addresses-for-pml4-table
		     lin-addr base-addr x86)
		    r-w-x x86))))
   :hints (("Goal"
	    :cases
	    (
	     ;; All different

	     ;; All same, except PML4TE
	     (and
	      (not (equal (pml4-table-entry-addr lin-addr base-addr)
			  (page-dir-ptr-table-entry-addr
			   lin-addr
			   (ash
			    (loghead
			     40
			     (logtail 12
				      (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
						 x86)))
			    12))))
	      (equal (page-dir-ptr-table-entry-addr
		      lin-addr
		      (ash
		       (loghead
			40
			(logtail 12
				 (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
					    x86)))
		       12))
		     (page-directory-entry-addr
		      lin-addr
		      (ash
		       (loghead
			40
			(logtail
			 12
			 (rm-low-64 (page-dir-ptr-table-entry-addr
				     lin-addr
				     (ash
				      (loghead
				       40
				       (logtail 12
						(rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
							   x86)))
				      12))
				    x86)))
		       12)))
	      (equal (page-directory-entry-addr
		      lin-addr
		      (ash
		       (loghead
			40
			(logtail
			 12
			 (rm-low-64 (page-dir-ptr-table-entry-addr
				     lin-addr
				     (ash
				      (loghead
				       40
				       (logtail 12
						(rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
							   x86)))
				      12))
				    x86)))
		       12))
		     (page-table-entry-addr
		      lin-addr
		      (ash
		       (loghead
			40
			(logtail
			 12
			 (rm-low-64
			  (page-directory-entry-addr
			   lin-addr
			   (ash
			    (loghead
			     40
			     (logtail
			      12
			      (rm-low-64
			       (page-dir-ptr-table-entry-addr
				lin-addr
				(ash
				 (loghead
				  40
				  (logtail
				   12
				   (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
					      x86)))
				 12))
			       x86)))
			    12))
			  x86)))
		       12))))


	     ;; PML4TE == PDE; PDPTE == PTE, PML4TE != PDPTE
	     (and
	      (equal (pml4-table-entry-addr lin-addr base-addr)
		     (page-directory-entry-addr
		      lin-addr
		      (ash
		       (loghead
			40
			(logtail
			 12
			 (rm-low-64 (page-dir-ptr-table-entry-addr
				     lin-addr
				     (ash
				      (loghead
				       40
				       (logtail 12
						(rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
							   x86)))
				      12))
				    x86)))
		       12)))
	      (equal
	       (page-dir-ptr-table-entry-addr
		lin-addr
		(ash
		 (loghead
		  40
		  (logtail 12
			   (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
				      x86)))
		 12))
	       (page-table-entry-addr
		lin-addr
		(ash
		 (loghead
		  40
		  (logtail
		   12
		   (rm-low-64
		    (page-directory-entry-addr
		     lin-addr
		     (ash
		      (loghead
		       40
		       (logtail
			12
			(rm-low-64
			 (page-dir-ptr-table-entry-addr
			  lin-addr
			  (ash
			   (loghead
			    40
			    (logtail
			     12
			     (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
					x86)))
			   12))
			 x86)))
		      12))
		    x86)))
		 12)))
	      (not
	       (equal
		(pml4-table-entry-addr lin-addr base-addr)
		(page-dir-ptr-table-entry-addr
		 lin-addr
		 (ash
		  (loghead
		   40
		   (logtail 12
			    (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
				       x86)))
		  12)))))

	     ;; All same.
	     (and
	      (equal (pml4-table-entry-addr lin-addr base-addr)
		     (page-dir-ptr-table-entry-addr
		      lin-addr
		      (ash
		       (loghead
			40
			(logtail 12
				 (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
					    x86)))
		       12)))
	      (equal (page-dir-ptr-table-entry-addr
		      lin-addr
		      (ash
		       (loghead
			40
			(logtail 12
				 (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
					    x86)))
		       12))
		     (page-directory-entry-addr
		      lin-addr
		      (ash
		       (loghead
			40
			(logtail
			 12
			 (rm-low-64 (page-dir-ptr-table-entry-addr
				     lin-addr
				     (ash
				      (loghead
				       40
				       (logtail 12
						(rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
							   x86)))
				      12))
				    x86)))
		       12)))
	      (equal (page-directory-entry-addr
		      lin-addr
		      (ash
		       (loghead
			40
			(logtail
			 12
			 (rm-low-64 (page-dir-ptr-table-entry-addr
				     lin-addr
				     (ash
				      (loghead
				       40
				       (logtail 12
						(rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
							   x86)))
				      12))
				    x86)))
		       12))
		     (page-table-entry-addr
		      lin-addr
		      (ash
		       (loghead
			40
			(logtail
			 12
			 (rm-low-64
			  (page-directory-entry-addr
			   lin-addr
			   (ash
			    (loghead
			     40
			     (logtail
			      12
			      (rm-low-64
			       (page-dir-ptr-table-entry-addr
				lin-addr
				(ash
				 (loghead
				  40
				  (logtail
				   12
				   (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
					      x86)))
				 12))
			       x86)))
			    12))
			  x86)))
		       12)))
	      (equal (page-table-entry-addr
		      lin-addr
		      (ash
		       (loghead
			40
			(logtail
			 12
			 (rm-low-64
			  (page-directory-entry-addr
			   lin-addr
			   (ash
			    (loghead
			     40
			     (logtail
			      12
			      (rm-low-64
			       (page-dir-ptr-table-entry-addr
				lin-addr
				(ash
				 (loghead
				  40
				  (logtail
				   12
				   (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
					      x86)))
				 12))
			       x86)))
			    12))
			  x86)))
		       12))
		     (pml4-table-entry-addr lin-addr base-addr)))
	     )
	    :in-theory (e/d* (ia32e-la-to-pa-pml4-table
			      wm-low-64-and-rm-low-64-writing-the-read
			      xlate-governing-qword-addresses-for-pml4-table
			      ;; xlate-governing-qword-addresses-for-page-dir-ptr-table
			      ;; xlate-governing-qword-addresses-for-page-directory
			      ;; xlate-governing-qword-addresses-for-page-table
			      )
			     (bitops::logand-with-negated-bitmask
			      accessed-bit
			      dirty-bit))))))

(defthm mv-nth-2-ia32e-la-to-pa-pml4-table-in-terms-of-updates
  (implies
   (and
    (xr :page-structure-marking-mode 0 x86)
    (not
     (mv-nth 0
	     (ia32e-la-to-pa-pml4-table
	      lin-addr base-addr wp smep
	      smap ac nxe r-w-x cpl x86)))
    (x86p x86)
    (canonical-address-p lin-addr)
    (physical-address-p base-addr)
    (equal (loghead 12 base-addr) 0))
   (equal (mv-nth
	   2
	   (ia32e-la-to-pa-pml4-table
	    lin-addr base-addr wp smep smap ac nxe r-w-x cpl x86))
	  (mv-nth 1
		  (update-a/d-bits
		   (xlate-governing-qword-addresses-for-pml4-table
		    lin-addr base-addr x86)
		   r-w-x x86))))
  :hints (("Goal"
	   :cases (
		   ;; 1g pages
		   (equal (page-size
			   (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr (ash
									       (loghead
										40
										(logtail 12
											 (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
												    x86)))
									       12)) x86))
			  1)
		   ;; 2m pages
		   (and
		    (equal (page-size
			    (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr (ash
										(loghead
										 40
										 (logtail 12
											  (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
												     x86)))
										12)) x86))
			   0)
		    (equal (page-size
			    (rm-low-64 (page-directory-entry-addr
					lin-addr
					(ash
					 (loghead
					  40
					  (logtail
					   12
					   (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr (ash
											       (loghead
												40
												(logtail 12
													 (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
														    x86)))
											       12))
						      x86)))
					 12))
				       x86))
			   1))
		   ;; 4k pages
		   (and
		    (equal (page-size
			    (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr (ash
										(loghead
										 40
										 (logtail 12
											  (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
												     x86)))
										12)) x86))
			   0)
		    (equal (page-size
			    (rm-low-64 (page-directory-entry-addr
					lin-addr
					(ash
					 (loghead
					  40
					  (logtail
					   12
					   (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr (ash
											       (loghead
												40
												(logtail 12
													 (rm-low-64 (pml4-table-entry-addr lin-addr base-addr)
														    x86)))
											       12))
						      x86)))
					 12))
				       x86))
			   0)))
	   :in-theory (e/d* (mv-nth-2-ia32e-la-to-pa-pml4-table-in-terms-of-updates-1G-pages
			     mv-nth-2-ia32e-la-to-pa-pml4-table-in-terms-of-updates-2M-pages
			     mv-nth-2-ia32e-la-to-pa-pml4-table-in-terms-of-updates-4K-pages)
			    (bitops::logand-with-negated-bitmask
			     accessed-bit
			     dirty-bit)))))
