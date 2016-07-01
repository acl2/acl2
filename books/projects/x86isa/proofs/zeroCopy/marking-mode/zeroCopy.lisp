;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

(include-book "system-level-mode/marking-mode-top" :dir :proof-utils)
(include-book "zeroCopy-part-1")
(include-book "zeroCopy-part-2")

(include-book "centaur/bitops/ihs-extensions" :dir :system)
(include-book "centaur/bitops/signed-byte-p" :dir :system)
(include-book "arithmetic/top-with-meta" :dir :system)
(include-book "centaur/gl/gl" :dir :system)

;; ======================================================================

(local
 (in-theory
  ;; For the effects theorems:
  (e/d* (instruction-decoding-and-spec-rules
	 shr-spec
	 shr-spec-64
	 sal/shl-spec
	 sal/shl-spec-64
	 gpr-and-spec-1
	 gpr-and-spec-4
	 gpr-and-spec-8
	 gpr-sub-spec-8
	 gpr-or-spec-8
	 gpr-xor-spec-4
	 jcc/cmovcc/setcc-spec
	 top-level-opcode-execute
	 two-byte-opcode-decode-and-execute
	 x86-operand-from-modr/m-and-sib-bytes
	 x86-effective-addr
	 x86-effective-addr-from-sib
	 x86-operand-to-reg/mem
	 rr08 rr32 rr64 wr08 wr32 wr64
	 rim08 rim32 rim64
	 !flgi-undefined
	 write-user-rflags

	 pos
	 mv-nth-0-las-to-pas-subset-p
	 member-p
	 subset-p

	 rb-alt-wb-equal-in-system-level-mode)

	(rewire_dst_to_src-disable
	 rewire_dst_to_src-disable-more))))

;; Argh, ACL2's default ancestors-check is killing me --- it prevents
;; x86-fetch-decode-execute from opening up (because the first hyp of
;; get-prefixes-alt-opener-lemma-no-prefix-byte is judged more
;; complicated than its ancestors --- why?). So I'm going to use Sol's
;; trivial ancestors-check version.
(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (acl2::use-trivial-ancestors-check))

(defthmd rewrite-to-pml4-table-entry-addr
  (implies
   (and (x86-state-okp x86)
	(source-addresses-ok-p x86)
	(destination-addresses-ok-p x86))

   (and
    (equal
     (logior (logand -4096 (logext 64 (xr :ctr *cr3* x86)))
	     (logand 4088
		     (loghead 28 (logtail 36 (xr :rgf *rdi* x86)))))
     (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)))
    (equal
     (logior (logand -4096 (logext 64 (xr :ctr *cr3* x86)))
	     (logand 4088
		     (loghead 28 (logtail 36 (xr :rgf *rsi* x86)))))
     (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86))))))

(defthmd rewrite-to-page-dir-ptr-table-entry-addr
  (implies
   (and (x86-state-okp x86)
	(source-addresses-ok-p x86)
	(source-pml4te-ok-p x86)
	(destination-addresses-ok-p x86)
	(destination-pml4te-ok-p x86))
   (and
    (equal
     (logior
      (logand 4088
	      (loghead 32 (logtail 27 (xr :rgf *rdi* x86))))
      (ash
       (loghead
	40
	(logtail
	 12
	 (combine-bytes
	  (mv-nth
	   1
	   (rb
	    (create-canonical-address-list
	     8
	     (logior
	      (logand -4096 (logext 64 (xr :ctr *cr3* x86)))
	      (logand 4088
		      (loghead 28 (logtail 36 (xr :rgf *rdi* x86))))))
	    :r x86)))))
       12))
     (page-dir-ptr-table-entry-addr
      (xr :rgf *rdi* x86)
      (pdpt-base-addr (xr :rgf *rdi* x86) x86)))
    (equal
     (logior
      (logand 4088
	      (loghead 32 (logtail 27 (xr :rgf *rsi* x86))))
      (ash
       (loghead
	40
	(logtail
	 12
	 (combine-bytes
	  (mv-nth
	   1
	   (rb
	    (create-canonical-address-list
	     8
	     (logior
	      (logand -4096 (logext 64 (xr :ctr *cr3* x86)))
	      (logand 4088
		      (loghead 28 (logtail 36 (xr :rgf *rsi* x86))))))
	    :r x86)))))
       12))
     (page-dir-ptr-table-entry-addr
      (xr :rgf *rsi* x86)
      (pdpt-base-addr (xr :rgf *rsi* x86) x86))))))

(defun-nx rewire_dst_to_src-effects-preconditions (x86)
  (and
   (x86-state-okp x86)
   (program-ok-p x86)
   (stack-ok-p x86)
   (program-and-stack-no-interfere-p x86)
   (source-addresses-ok-p x86)
   (source-PML4TE-ok-p x86)
   (source-PDPTE-ok-p x86)
   (source-PML4TE-and-stack-no-interfere-p x86)
   (source-PML4TE-and-program-no-interfere-p x86)
   (source-PDPTE-and-stack-no-interfere-p x86)
   (source-PDPTE-and-program-no-interfere-p x86)
   (source-PDPTE-and-source-PML4E-no-interfere-p x86)
   (destination-addresses-ok-p x86)
   (destination-PML4TE-ok-p x86)
   (destination-PDPTE-ok-p x86)
   (destination-PML4TE-and-stack-no-interfere-p x86)
   (destination-PML4TE-and-program-no-interfere-p x86)
   (destination-PML4TE-and-source-PML4TE-no-interfere-p x86)
   (destination-PML4TE-and-source-PDPTE-no-interfere-p x86)
   (destination-PDPTE-and-source-PML4E-no-interfere-p x86)
   (destination-PDPTE-and-source-PDPTE-no-interfere-p x86)
   (destination-PDPTE-and-destination-PML4TE-no-interfere-p x86)
   (destination-PDPTE-and-stack-no-interfere-p x86)
   (destination-PDPTE-and-program-no-interfere-p x86)
   (return-address-ok-p x86)
   (stack-containing-return-address-ok-p x86)
   (stack-containing-return-address-and-program-no-interfere-p x86)
   (stack-containing-return-address-and-source-PML4E-no-interfere-p x86)
   (stack-containing-return-address-and-source-PDPTE-no-interfere-p x86)
   (stack-containing-return-address-and-destination-PML4E-no-interfere-p x86)
   (stack-containing-return-address-and-destination-PDPTE-no-interfere-p x86)
   (stack-containing-return-address-and-rest-of-the-stack-no-interfere-p x86)

   (direct-map-p
    8
    (page-dir-ptr-table-entry-addr
     (xr :rgf *rsi* x86)
     (pdpt-base-addr (xr :rgf *rsi* x86) x86))
    :w (cpl x86) x86)))

(def-ruleset rewire_dst_to_src-effects-preconditions-defs
  '(x86-state-okp
    program-ok-p
    stack-ok-p
    program-and-stack-no-interfere-p
    source-addresses-ok-p
    source-pml4te-ok-p source-pdpte-ok-p
    source-pml4te-and-stack-no-interfere-p
    source-pml4te-and-program-no-interfere-p
    source-pdpte-and-stack-no-interfere-p
    source-pdpte-and-program-no-interfere-p
    source-pdpte-and-source-pml4e-no-interfere-p
    destination-addresses-ok-p
    destination-pml4te-ok-p
    destination-pdpte-ok-p
    destination-pml4te-and-stack-no-interfere-p
    destination-pml4te-and-program-no-interfere-p
    destination-pml4te-and-source-pml4te-no-interfere-p
    destination-pml4te-and-source-pdpte-no-interfere-p
    destination-pdpte-and-source-pml4e-no-interfere-p
    destination-pdpte-and-source-pdpte-no-interfere-p
    destination-pdpte-and-destination-pml4te-no-interfere-p
    destination-pdpte-and-stack-no-interfere-p
    destination-pdpte-and-program-no-interfere-p
    return-address-ok-p
    stack-containing-return-address-ok-p
    stack-containing-return-address-and-program-no-interfere-p
    stack-containing-return-address-and-source-pml4e-no-interfere-p
    stack-containing-return-address-and-source-pdpte-no-interfere-p
    stack-containing-return-address-and-destination-pml4e-no-interfere-p
    stack-containing-return-address-and-destination-pdpte-no-interfere-p
    stack-containing-return-address-and-rest-of-the-stack-no-interfere-p))

(defthmd rewire_dst_to_src-effects
  (implies
   (rewire_dst_to_src-effects-preconditions x86)
   (equal
    (x86-run (rewire_dst_to_src-clk) x86)
    (xw
     :rgf *rax* 1
     (xw
      :rgf *rcx*
      (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86))
      (xw
       :rgf *rdx*
       (logand
	4503598553628672
	(logior
	 (logand
	  -4503598553628673
	  (logext
	   64
	   (combine-bytes
	    (mv-nth
	     1
	     (rb
	      (create-canonical-address-list
	       8
	       (page-dir-ptr-table-entry-addr
		(xr :rgf *rsi* x86)
		(pdpt-base-addr (xr :rgf *rsi* x86) x86)))
	      :r x86)))))
	 (logand
	  4503598553628672
	  (logext
	   64
	   (combine-bytes
	    (mv-nth
	     1
	     (rb
	      (create-canonical-address-list
	       8
	       (page-dir-ptr-table-entry-addr
		(xr :rgf *rdi* x86)
		(pdpt-base-addr (xr :rgf *rdi* x86) x86)))
	      :r x86)))))))
       (xw
	:rgf *rsp* (+ 8 (xr :rgf *rsp* x86))
	(xw
	 :rgf *rsi* 0
	 (xw
	  :rgf *rdi*
	  (logand
	   4503598553628672
	   (logext
	    64
	    (combine-bytes
	     (mv-nth
	      1
	      (rb
	       (create-canonical-address-list
		8
		(page-dir-ptr-table-entry-addr
		 (xr :rgf *rdi* x86)
		 (pdpt-base-addr (xr :rgf *rdi* x86) x86)))
	       :r x86)))))
	  (xw
	   :rgf *r8* 1099511627775
	   (xw
	    :rgf *r9*
	    (logand
	     4503598553628672
	     (logext
	      64
	      (combine-bytes
	       (mv-nth
		1
		(rb
		 (create-canonical-address-list
		  8
		  (page-dir-ptr-table-entry-addr
		   (xr :rgf *rdi* x86)
		   (pdpt-base-addr (xr :rgf *rdi* x86) x86)))
		 :r x86)))))
	    (xw
	     :rip 0
	     (logext
	      64
	      (combine-bytes
	       (mv-nth 1
		       (rb (create-canonical-address-list 8 (xr :rgf *rsp* x86))
			   :r x86))))
	     (xw
	      :undef 0 (+ 46 (nfix (xr :undef 0 x86)))
	      (!flgi
	       *cf*
	       (bool->bit
		(<
		 (logand
		  4503598553628672
		  (combine-bytes
		   (mv-nth
		    1
		    (rb
		     (create-canonical-address-list
		      8
		      (page-dir-ptr-table-entry-addr
		       (xr :rgf *rdi* x86)
		       (pdpt-base-addr (xr :rgf *rdi* x86) x86)))
		     :r x86))))
		 (logand
		  4503598553628672
		  (logior
		   (logand
		    18442240475155922943
		    (combine-bytes
		     (mv-nth
		      1
		      (rb
		       (create-canonical-address-list
			8
			(page-dir-ptr-table-entry-addr
			 (xr :rgf *rsi* x86)
			 (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
		       :r x86))))
		   (logand
		    4503598553628672
		    (combine-bytes
		     (mv-nth
		      1
		      (rb
		       (create-canonical-address-list
			8
			(page-dir-ptr-table-entry-addr
			 (xr :rgf *rdi* x86)
			 (pdpt-base-addr (xr :rgf *rdi* x86) x86)))
		       :r x86))))))))
	       (!flgi
		*pf*
		(pf-spec64
		 (loghead
		  64
		  (+
		   (logand
		    4503598553628672
		    (logext
		     64
		     (combine-bytes
		      (mv-nth
		       1
		       (rb
			(create-canonical-address-list
			 8
			 (page-dir-ptr-table-entry-addr
			  (xr :rgf *rdi* x86)
			  (pdpt-base-addr (xr :rgf *rdi* x86) x86)))
			:r x86)))))
		   (-
		    (logand
		     4503598553628672
		     (logior
		      (logand
		       -4503598553628673
		       (logext
			64
			(combine-bytes
			 (mv-nth
			  1
			  (rb
			   (create-canonical-address-list
			    8
			    (page-dir-ptr-table-entry-addr
			     (xr :rgf *rsi* x86)
			     (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
			   :r x86)))))
		      (logand
		       4503598553628672
		       (logext
			64
			(combine-bytes
			 (mv-nth
			  1
			  (rb
			   (create-canonical-address-list
			    8
			    (page-dir-ptr-table-entry-addr
			     (xr :rgf *rdi* x86)
			     (pdpt-base-addr (xr :rgf *rdi* x86) x86)))
			   :r x86)))))))))))
		(!flgi
		 *af*
		 (sub-af-spec64
		  (logand
		   4503598553628672
		   (combine-bytes
		    (mv-nth
		     1
		     (rb
		      (create-canonical-address-list
		       8
		       (page-dir-ptr-table-entry-addr
			(xr :rgf *rdi* x86)
			(pdpt-base-addr (xr :rgf *rdi* x86) x86)))
		      :r x86))))
		  (logand
		   4503598553628672
		   (logior
		    (logand
		     18442240475155922943
		     (combine-bytes
		      (mv-nth
		       1
		       (rb
			(create-canonical-address-list
			 8
			 (page-dir-ptr-table-entry-addr
			  (xr :rgf *rsi* x86)
			  (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
			:r x86))))
		    (logand
		     4503598553628672
		     (combine-bytes
		      (mv-nth
		       1
		       (rb
			(create-canonical-address-list
			 8
			 (page-dir-ptr-table-entry-addr
			  (xr :rgf *rdi* x86)
			  (pdpt-base-addr (xr :rgf *rdi* x86) x86)))
			:r x86)))))))
		 (!flgi
		  *zf* 1
		  (!flgi
		   *sf*
		   (sf-spec64
		    (loghead
		     64
		     (+
		      (logand
		       4503598553628672
		       (logext
			64
			(combine-bytes
			 (mv-nth
			  1
			  (rb
			   (create-canonical-address-list
			    8
			    (page-dir-ptr-table-entry-addr
			     (xr :rgf *rdi* x86)
			     (pdpt-base-addr (xr :rgf *rdi* x86) x86)))
			   :r x86)))))
		      (-
		       (logand
			4503598553628672
			(logior
			 (logand
			  -4503598553628673
			  (logext
			   64
			   (combine-bytes
			    (mv-nth
			     1
			     (rb
			      (create-canonical-address-list
			       8
			       (page-dir-ptr-table-entry-addr
				(xr :rgf *rsi* x86)
				(pdpt-base-addr (xr :rgf *rsi* x86) x86)))
			      :r x86)))))
			 (logand
			  4503598553628672
			  (logext
			   64
			   (combine-bytes
			    (mv-nth
			     1
			     (rb
			      (create-canonical-address-list
			       8
			       (page-dir-ptr-table-entry-addr
				(xr :rgf *rdi* x86)
				(pdpt-base-addr (xr :rgf *rdi* x86) x86)))
			      :r x86)))))))))))
		   (!flgi
		    *of*
		    (of-spec64
		     (+
		      (logand
		       4503598553628672
		       (logext
			64
			(combine-bytes
			 (mv-nth
			  1
			  (rb
			   (create-canonical-address-list
			    8
			    (page-dir-ptr-table-entry-addr
			     (xr :rgf *rdi* x86)
			     (pdpt-base-addr (xr :rgf *rdi* x86) x86)))
			   :r x86)))))
		      (-
		       (logand
			4503598553628672
			(logior
			 (logand
			  -4503598553628673
			  (logext
			   64
			   (combine-bytes
			    (mv-nth
			     1
			     (rb
			      (create-canonical-address-list
			       8
			       (page-dir-ptr-table-entry-addr
				(xr :rgf *rsi* x86)
				(pdpt-base-addr (xr :rgf *rsi* x86) x86)))
			      :r x86)))))
			 (logand
			  4503598553628672
			  (logext
			   64
			   (combine-bytes
			    (mv-nth
			     1
			     (rb
			      (create-canonical-address-list
			       8
			       (page-dir-ptr-table-entry-addr
				(xr :rgf *rdi* x86)
				(pdpt-base-addr (xr :rgf *rdi* x86) x86)))
			      :r x86))))))))))
		    (mv-nth
		     2
		     (las-to-pas
		      (create-canonical-address-list 8 (xr :rgf *rsp* x86))
		      :r 0
		      (mv-nth
		       2
		       (las-to-pas
			(create-canonical-address-list
			 40 (+ 206 (xr :rip 0 x86)))
			:x 0
			(mv-nth
			 2
			 (las-to-pas
			  (create-canonical-address-list
			   15 (+ 190 (xr :rip 0 x86)))
			  :x 0
			  (mv-nth
			   1
			   (wb
			    (create-addr-bytes-alist
			     (create-canonical-address-list
			      8
			      (page-dir-ptr-table-entry-addr
			       (xr :rgf *rsi* x86)
			       (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
			     (byte-ify
			      8
			      (logior
			       (logand
				18442240475155922943
				(combine-bytes
				 (mv-nth
				  1
				  (rb
				   (create-canonical-address-list
				    8
				    (page-dir-ptr-table-entry-addr
				     (xr :rgf *rsi* x86)
				     (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
				   :r x86))))
			       (logand
				4503598553628672
				(combine-bytes
				 (mv-nth
				  1
				  (rb
				   (create-canonical-address-list
				    8
				    (page-dir-ptr-table-entry-addr
				     (xr :rgf *rdi* x86)
				     (pdpt-base-addr (xr :rgf *rdi* x86) x86)))
				   :r x86)))))))
			    (mv-nth
			     2
			     (las-to-pas
			      (create-canonical-address-list
			       6 (+ 184 (xr :rip 0 x86)))
			      :x 0
			      (mv-nth
			       2
			       (las-to-pas
				(create-canonical-address-list
				 8
				 (page-dir-ptr-table-entry-addr
				  (xr :rgf *rsi* x86)
				  (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
				:r 0
				(mv-nth
				 2
				 (las-to-pas
				  (create-canonical-address-list
				   40 (+ 144 (xr :rip 0 x86)))
				  :x 0
				  (mv-nth
				   2
				   (las-to-pas
				    (create-canonical-address-list
				     3 (+ 140 (xr :rip 0 x86)))
				    :x 0
				    (mv-nth
				     2
				     (las-to-pas
				      (create-canonical-address-list
				       8
				       (pml4-table-entry-addr
					(xr :rgf *rsi* x86)
					(pml4-table-base-addr x86)))
				      :r 0
				      (mv-nth
				       2
				       (las-to-pas
					(create-canonical-address-list
					 32 (+ 108 (xr :rip 0 x86)))
					:x 0
					(mv-nth
					 2
					 (las-to-pas
					  (create-canonical-address-list
					   18 (+ 86 (xr :rip 0 x86)))
					  :x 0
					  (mv-nth
					   2
					   (las-to-pas
					    (create-canonical-address-list
					     8
					     (page-dir-ptr-table-entry-addr
					      (xr :rgf *rdi* x86)
					      (pdpt-base-addr (xr :rgf *rdi* x86) x86)))
					    :r 0
					    (mv-nth
					     2
					     (las-to-pas
					      (create-canonical-address-list
					       40 (+ 46 (xr :rip 0 x86)))
					      :x 0
					      (mv-nth
					       2
					       (las-to-pas
						(create-canonical-address-list
						 4 (+ 38 (xr :rip 0 x86)))
						:x 0
						(mv-nth
						 2
						 (las-to-pas
						  (create-canonical-address-list
						   8
						   (pml4-table-entry-addr
						    (xr :rgf *rdi* x86)
						    (pml4-table-base-addr x86)))
						  :r 0
						  (mv-nth
						   2
						   (las-to-pas
						    (create-canonical-address-list
						     25 (+ 13 (xr :rip 0 x86)))
						    :x 0
						    (mv-nth
						     2
						     (las-to-pas
						      (create-canonical-address-list
						       8
						       (+ -24 (xr :rgf *rsp* x86)))
						      :r 0
						      (mv-nth
						       2
						       (las-to-pas
							(create-canonical-address-list
							 5 (+ 8 (xr :rip 0 x86)))
							:x 0
							(mv-nth
							 1
							 (wb
							  (create-addr-bytes-alist
							   (create-canonical-address-list
							    8
							    (+ -24 (xr :rgf *rsp* x86)))
							   (byte-ify
							    8
							    (xr :ctr *cr3* x86)))
							  (mv-nth
							   2
							   (las-to-pas
							    (create-canonical-address-list
							     8 (xr :rip 0 x86))
							    :x 0
							    x86))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  :hints (("Goal"
	   :expand ((:free (x) (hide x))
		    (rewire_dst_to_src-effects-preconditions x86))
	   :use ((:instance x86-run-plus
			    (n1 (rewire_dst_to_src-clk-1-to-45))
			    (n2 (rewire_dst_to_src-clk-46-to-58)))
		 (:instance rewire_dst_to_src-effects-1-to-45-instructions)
		 (:instance rewire_dst_to_src-effects-46-to-58-instructions)
		 (:instance rewrite-to-pml4-table-entry-addr)
		 (:instance rewrite-to-page-dir-ptr-table-entry-addr))
	   :in-theory (union-theories
		       '(program-alt-ok-p-and-program-ok-p
			 natp
			 (natp)
			 rewire_dst_to_src-clk
			 rewire_dst_to_src-clk-1-to-45
			 rewire_dst_to_src-clk-46-to-58)
		       (theory 'minimal-theory)))))

(in-theory (e/d () ((rewire_dst_to_src-clk) rewire_dst_to_src-clk)))

;; (def-gl-thm test-mapped-address
;;   ;; Map the destination PDPTE to contain the same value (not
;;   ;; permissions) as that in the source PDPTE.
;;   :hyp (and (unsigned-byte-p 64 source-entry)
;;             (unsigned-byte-p 64 destination-entry))
;;   ;; pointer comes from the byte-list of wb in the following s-expr.
;;   :concl (let* ((pointer (logior
;;                           (logand     4503598553628672 source-entry)
;;                           (logand 18442240475155922943 destination-entry))))
;;            (equal (ash (part-select source-entry :low 30 :width 22) 30)
;;                   (ash (part-select      pointer :low 30 :width 22) 30)))
;;   :g-bindings
;;   (gl::auto-bindings (:mix (:nat source-entry 64) (:nat destination-entry 64))))

;; ======================================================================

(local
 (defthmd program-at-alt-in-final-state-==-program-at-in-final-state-helper-1
   (implies (rewire_dst_to_src-effects-preconditions x86)
	    (and
	     (not
	      (mv-nth 0
		      (las-to-pas
		       (create-canonical-address-list *rewire_dst_to_src-len* (xr :rip 0 x86))
		       :x (cpl x86) (x86-run (rewire_dst_to_src-clk) x86))))
	     (equal
	      (mv-nth 1
		      (las-to-pas
		       (create-canonical-address-list *rewire_dst_to_src-len* (xr :rip 0 x86))
		       :x (cpl x86) (x86-run (rewire_dst_to_src-clk) x86)))
	      (mv-nth 1
		      (las-to-pas
		       (create-canonical-address-list *rewire_dst_to_src-len* (xr :rip 0 x86))
		       :x (cpl x86) x86)))))
   :hints (("Goal"
	    :do-not-induct t
	    :hands-off (x86-run)
	    :use ((:instance rewire_dst_to_src-effects))
	    :in-theory (e/d* (disjoint-p-all-translation-governing-addresses-subset-p)
			     (
			      ;; x86-state-okp
			      ;; program-ok-p
			      ;; stack-ok-p
			      ;; program-and-stack-no-interfere-p
			      ;; source-addresses-ok-p
			      ;; source-pml4te-ok-p
			      ;; source-pdpte-ok-p
			      source-pml4te-and-stack-no-interfere-p
			      ;; source-pml4te-and-program-no-interfere-p
			      source-pdpte-and-stack-no-interfere-p
			      ;; source-pdpte-and-program-no-interfere-p
			      source-pdpte-and-source-pml4e-no-interfere-p
			      ;; destination-addresses-ok-p
			      ;; destination-pml4te-ok-p
			      ;; destination-pdpte-ok-p
			      destination-pml4te-and-stack-no-interfere-p
			      ;; destination-pml4te-and-program-no-interfere-p
			      destination-pml4te-and-source-pml4te-no-interfere-p
			      destination-pml4te-and-source-pdpte-no-interfere-p
			      destination-pdpte-and-source-pml4e-no-interfere-p
			      destination-pdpte-and-source-pdpte-no-interfere-p
			      destination-pdpte-and-destination-pml4te-no-interfere-p
			      destination-pdpte-and-stack-no-interfere-p
			      ;; destination-pdpte-and-program-no-interfere-p
			      return-address-ok-p
			      stack-containing-return-address-ok-p
			      ;; stack-containing-return-address-and-program-no-interfere-p
			      stack-containing-return-address-and-source-pml4e-no-interfere-p
			      stack-containing-return-address-and-source-pdpte-no-interfere-p
			      stack-containing-return-address-and-destination-pml4e-no-interfere-p
			      stack-containing-return-address-and-destination-pdpte-no-interfere-p
			      stack-containing-return-address-and-rest-of-the-stack-no-interfere-p

			      create-canonical-address-list
			      (:rewrite program-at-values-and-!flgi)
			      (:rewrite get-prefixes-opener-lemma-group-4-prefix-in-marking-mode)
			      (:rewrite rb-in-terms-of-rb-subset-p-in-system-level-mode)
			      (:rewrite get-prefixes-opener-lemma-group-3-prefix-in-marking-mode)
			      (:rewrite get-prefixes-opener-lemma-group-2-prefix-in-marking-mode)
			      (:rewrite get-prefixes-opener-lemma-group-1-prefix-in-marking-mode)
			      (:rewrite mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures)
			      (:rewrite mv-nth-2-rb-in-system-level-non-marking-mode)
			      (:rewrite rb-returns-x86-programmer-level-mode)
			      (:linear rm-low-64-logand-logior-helper-1)
			      (:definition n64p$inline)
			      (:type-prescription xlate-equiv-memory)
			      (:rewrite program-at-alt-wb-disjoint-in-system-level-mode)
			      (:type-prescription natp-page-dir-ptr-table-entry-addr)
			      mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs
			      mv-nth-2-las-to-pas-system-level-non-marking-mode
			      (:rewrite r/x-is-irrelevant-for-mv-nth-2-las-to-pas-when-no-errors)
			      (:rewrite acl2::cdr-of-append-when-consp)
			      (:rewrite acl2::car-of-append)
			      (:rewrite acl2::consp-of-append)
			      (:rewrite acl2::append-atom-under-list-equiv)
			      (:rewrite int-lists-in-seq-p-and-append)
			      (:type-prescription binary-append)
			      (:rewrite xr-fault-wb-in-system-level-mode)
			      (:type-prescription n01p-page-size)
			      (:type-prescription member-p-physical-address-p-physical-address-listp)
			      (:rewrite acl2::right-cancellation-for-+)
			      (:type-prescription member-p-physical-address-p)
			      (:rewrite acl2::append-singleton-under-set-equiv)
			      (:rewrite rewrite-rb-to-rb-alt)
			      (:rewrite acl2::loghead-identity)
			      (:definition subset-p)
			      (:rewrite
			       infer-disjointness-with-all-translation-governing-addresses-from-gather-all-paging-structure-qword-addresses-with-disjoint-p$)
			      (:meta acl2::mv-nth-cons-meta)
			      (:rewrite bitops::loghead-of-loghead-2)
			      (:type-prescription member-p)
			      (:rewrite mv-nth-0-las-to-pas-subset-p-with-l-addrs-from-bind-free)
			      (:rewrite member-p-canonical-address-listp)
			      (:rewrite right-shift-to-logtail)
			      (:rewrite two-mv-nth-1-las-to-pas-subset-p-disjoint-from-las-to-pas)
			      (:type-prescription binary-logand)
			      (:rewrite greater-logbitp-of-unsigned-byte-p . 2)
			      (:rewrite mv-nth-1-las-to-pas-subset-p)
			      (:rewrite combine-mv-nth-2-las-to-pas-same-r-w-x-when-addresses-in-sequence)
			      (:rewrite
			       int-lists-in-seq-p-and-append-with-create-canonical-address-list-2)
			      (:type-prescription int-lists-in-seq-p)
			      (:definition int-lists-in-seq-p)
			      (:rewrite xw-xw-intra-simple-field-shadow-writes)
			      (:rewrite page-dir-ptr-table-entry-addr-is-a-multiple-of-8)
			      (:rewrite gl::nfix-natp)))))))


(local
 (defthmd program-at-alt-in-final-state-==-program-at-in-final-state-helper-2
   (implies (rewire_dst_to_src-effects-preconditions x86)
	    (disjoint-p
	     ;; disjoint-p$
	     (mv-nth 1
		     (las-to-pas (create-canonical-address-list 272 (xr :rip 0 x86))
				 :x (cpl x86)
				 (x86-run (rewire_dst_to_src-clk) x86)))
	     (open-qword-paddr-list (gather-all-paging-structure-qword-addresses
				     (x86-run (rewire_dst_to_src-clk) x86)))))
   :hints (("Goal"
	    :do-not-induct t
	    :hands-off (x86-run)
	    :use ((:instance rewire_dst_to_src-effects)
		  (:instance program-at-alt-in-final-state-==-program-at-in-final-state-helper-1))
	    :in-theory (e/d* (page-size)
			     (
			      ;; x86-state-okp
			      ;; program-ok-p
			      ;; stack-ok-p
			      ;; program-and-stack-no-interfere-p
			      ;; source-addresses-ok-p
			      ;; source-pml4te-ok-p
			      ;; source-pdpte-ok-p
			      source-pml4te-and-stack-no-interfere-p
			      ;; source-pml4te-and-program-no-interfere-p
			      source-pdpte-and-stack-no-interfere-p
			      ;; source-pdpte-and-program-no-interfere-p
			      source-pdpte-and-source-pml4e-no-interfere-p
			      ;; destination-addresses-ok-p
			      ;; destination-pml4te-ok-p
			      ;; destination-pdpte-ok-p
			      destination-pml4te-and-stack-no-interfere-p
			      ;; destination-pml4te-and-program-no-interfere-p
			      destination-pml4te-and-source-pml4te-no-interfere-p
			      destination-pml4te-and-source-pdpte-no-interfere-p
			      destination-pdpte-and-source-pml4e-no-interfere-p
			      destination-pdpte-and-source-pdpte-no-interfere-p
			      destination-pdpte-and-destination-pml4te-no-interfere-p
			      destination-pdpte-and-stack-no-interfere-p
			      ;; destination-pdpte-and-program-no-interfere-p
			      return-address-ok-p
			      stack-containing-return-address-ok-p
			      ;; stack-containing-return-address-and-program-no-interfere-p
			      stack-containing-return-address-and-source-pml4e-no-interfere-p
			      stack-containing-return-address-and-source-pdpte-no-interfere-p
			      stack-containing-return-address-and-destination-pml4e-no-interfere-p
			      stack-containing-return-address-and-destination-pdpte-no-interfere-p
			      stack-containing-return-address-and-rest-of-the-stack-no-interfere-p

			      create-canonical-address-list
			      (:rewrite program-at-values-and-!flgi)
			      (:rewrite get-prefixes-opener-lemma-group-4-prefix-in-marking-mode)
			      (:rewrite rb-in-terms-of-rb-subset-p-in-system-level-mode)
			      (:rewrite get-prefixes-opener-lemma-group-3-prefix-in-marking-mode)
			      (:rewrite get-prefixes-opener-lemma-group-2-prefix-in-marking-mode)
			      (:rewrite get-prefixes-opener-lemma-group-1-prefix-in-marking-mode)
			      (:rewrite mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures)
			      (:rewrite mv-nth-2-rb-in-system-level-non-marking-mode)
			      (:rewrite rb-returns-x86-programmer-level-mode)
			      (:linear rm-low-64-logand-logior-helper-1)
			      (:definition n64p$inline)
			      (:type-prescription xlate-equiv-memory)
			      (:rewrite program-at-alt-wb-disjoint-in-system-level-mode)
			      (:type-prescription natp-page-dir-ptr-table-entry-addr)
			      mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs
			      mv-nth-2-las-to-pas-system-level-non-marking-mode
			      (:rewrite r/x-is-irrelevant-for-mv-nth-2-las-to-pas-when-no-errors)
			      (:rewrite acl2::cdr-of-append-when-consp)
			      (:rewrite acl2::car-of-append)
			      (:rewrite acl2::consp-of-append)
			      (:rewrite acl2::append-atom-under-list-equiv)
			      (:rewrite int-lists-in-seq-p-and-append)
			      (:type-prescription binary-append)
			      (:rewrite xr-fault-wb-in-system-level-mode)
			      (:type-prescription n01p-page-size)
			      (:type-prescription member-p-physical-address-p-physical-address-listp)
			      (:rewrite acl2::right-cancellation-for-+)
			      (:type-prescription member-p-physical-address-p)
			      (:rewrite acl2::append-singleton-under-set-equiv)
			      (:rewrite rewrite-rb-to-rb-alt)
			      (:rewrite acl2::loghead-identity)
			      (:definition subset-p)
			      (:rewrite
			       infer-disjointness-with-all-translation-governing-addresses-from-gather-all-paging-structure-qword-addresses-with-disjoint-p$)
			      (:meta acl2::mv-nth-cons-meta)
			      (:rewrite bitops::loghead-of-loghead-2)
			      (:type-prescription member-p)
			      (:rewrite mv-nth-0-las-to-pas-subset-p-with-l-addrs-from-bind-free)
			      (:rewrite member-p-canonical-address-listp)
			      (:rewrite right-shift-to-logtail)
			      (:rewrite two-mv-nth-1-las-to-pas-subset-p-disjoint-from-las-to-pas)
			      (:type-prescription binary-logand)
			      (:rewrite greater-logbitp-of-unsigned-byte-p . 2)
			      (:rewrite mv-nth-1-las-to-pas-subset-p)
			      (:rewrite combine-mv-nth-2-las-to-pas-same-r-w-x-when-addresses-in-sequence)
			      (:rewrite
			       int-lists-in-seq-p-and-append-with-create-canonical-address-list-2)
			      (:type-prescription int-lists-in-seq-p)
			      (:definition int-lists-in-seq-p)
			      (:rewrite xw-xw-intra-simple-field-shadow-writes)
			      (:rewrite page-dir-ptr-table-entry-addr-is-a-multiple-of-8)
			      (:rewrite gl::nfix-natp)))))))

(local
 (defthmd program-at-alt-in-final-state-==-program-at-in-final-state-helper-3
   (implies (rewire_dst_to_src-effects-preconditions x86)
	    (disjoint-p$
	     (mv-nth 1
		     (las-to-pas (create-canonical-address-list 272 (xr :rip 0 x86))
				 :x (cpl x86)
				 (x86-run (rewire_dst_to_src-clk) x86)))
	     (open-qword-paddr-list (gather-all-paging-structure-qword-addresses
				     (x86-run (rewire_dst_to_src-clk) x86)))))
   :hints (("Goal"
	    :do-not-induct t
	    :hands-off (x86-run disjoint-p)
	    :use ((:instance program-at-alt-in-final-state-==-program-at-in-final-state-helper-2))
	    :in-theory (e/d* (disjoint-p$)
			     (rewire_dst_to_src-effects-preconditions))))))

;; ======================================================================

(defthmd rewire_dst_to_src-effects-preconditions-and-ms-fault-programmer-level-and-marking-mode-fields
  (implies (rewire_dst_to_src-effects-preconditions x86)
	   (and (equal (xr :ms                          0 x86) nil)
		(equal (xr :fault                       0 x86) nil)
		(equal (xr :programmer-level-mode       0 x86) nil)
		(equal (xr :page-structure-marking-mode 0 x86) t))))

(defthmd fault-from-final-state
  (implies (rewire_dst_to_src-effects-preconditions x86)
	   (equal (xr :fault                       0 (x86-run (rewire_dst_to_src-clk) x86))
		  (xr :fault                       0 x86)))
  :hints (("Goal"
	   :do-not '(preprocess)
	   :use ((:instance rewire_dst_to_src-effects))
	   :hands-off (x86-run)
	   :in-theory (e/d*
		       (disjoint-p-all-translation-governing-addresses-subset-p)
		       (x86-fetch-decode-execute-opener-in-marking-mode
			mv-nth-0-rb-and-mv-nth-0-las-to-pas-in-system-level-mode
			mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures
			two-mv-nth-1-las-to-pas-subset-p-disjoint-from-las-to-pas
			combine-mv-nth-2-las-to-pas-same-r-w-x-when-addresses-in-sequence
			mv-nth-2-las-to-pas-system-level-non-marking-mode
			mv-nth-2-get-prefixes-alt-no-prefix-byte
			rm08-to-rb
			rewrite-rb-to-rb-alt
			page-dir-ptr-table-entry-addr-to-c-program-optimized-form
			unsigned-byte-p-52-of-left-shifting-a-40-bit-vector-by-12
			unsigned-byte-p-of-combine-bytes-and-rb-in-system-level-mode
			mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs
			subset-p
			(:meta acl2::mv-nth-cons-meta)
			create-canonical-address-list
			acl2::loghead-identity
			n64p$inline
			(:r greater-logbitp-of-unsigned-byte-p . 2)
			xr-fault-wb-in-system-level-mode
			xw-xw-intra-simple-field-shadow-writes
			unsigned-byte-p-of-loghead
			r/x-is-irrelevant-for-mv-nth-2-las-to-pas-when-no-errors
			canonical-address-p-pml4-table-entry-addr-to-c-program-optimized-form
			right-shift-to-logtail
			bitops::loghead-of-loghead-2
			bitops::logand-with-bitmask
			(:linear rm-low-64-logand-logior-helper-1)
			(:t binary-logior)
			(:t binary-logand)
			force (force))))))

(defthmd ms-fault-programmer-level-and-marking-mode-from-final-state
  (implies (rewire_dst_to_src-effects-preconditions x86)
	   (and (equal (xr :ms                          0 (x86-run (rewire_dst_to_src-clk) x86)) nil)
		(equal (xr :fault                       0 (x86-run (rewire_dst_to_src-clk) x86)) nil)
		(equal (xr :programmer-level-mode       0 (x86-run (rewire_dst_to_src-clk) x86)) nil)
		(equal (xr :page-structure-marking-mode 0 (x86-run (rewire_dst_to_src-clk) x86)) t)))
  :hints (("Goal"
	   :do-not '(preprocess)
	   :use ((:instance rewire_dst_to_src-effects)
		 (:instance fault-from-final-state))
	   :hands-off (x86-run)
	   :in-theory (e/d*
		       (rewire_dst_to_src-effects-preconditions-and-ms-fault-programmer-level-and-marking-mode-fields)
		       (rewire_dst_to_src-effects-preconditions)))))

;; ======================================================================

;; Some more preconditions:

(defun-nx more-stack-containing-return-address-and-source-PML4E-no-interfere-p (x86)
  ;; Physical addresses corresponding to source PML4TE are disjoint
  ;; from the translation-governing addresses of the stack containing
  ;; the return address.
  (disjoint-p
   (mv-nth 1 (las-to-pas
	      (create-canonical-address-list
	       8
	       (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)))
	      :r (cpl x86) x86))
   (all-translation-governing-addresses
    (create-canonical-address-list 8 (xr :rgf *rsp* x86))
    x86)))

(defun-nx more-destination-PDPTE-and-source-PML4E-no-interfere-p (x86)
  (and
   (disjoint-p
    (mv-nth 1 (las-to-pas
	       (create-canonical-address-list
		8
		(page-dir-ptr-table-entry-addr
		 (xr :rgf *rsi* x86)
		 (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
	       :w (cpl x86) x86))
    (mv-nth 1 (las-to-pas
	       (create-canonical-address-list
		8
		(pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)))
	       :r (cpl x86) x86)))
   (disjoint-p
    (mv-nth 1 (las-to-pas
	       (create-canonical-address-list
		8
		(pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)))
	       :r (cpl x86) x86))
    (all-translation-governing-addresses
     (create-canonical-address-list
      8
      (page-dir-ptr-table-entry-addr
       (xr :rgf *rsi* x86)
       (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
     x86))))

(defun-nx more-destination-PML4TE-and-source-PML4TE-no-interfere-p (x86)
  (disjoint-p
   (mv-nth
    1
    (las-to-pas (create-canonical-address-list
		 8
		 (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)))
		:r (cpl x86) x86))
   (all-translation-governing-addresses
    (create-canonical-address-list
     8
     (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86)))
    x86)))

(defun-nx more-source-PDPTE-and-source-PML4E-no-interfere-p (x86)
  (disjoint-p
   (mv-nth 1 (las-to-pas
	      (create-canonical-address-list
	       8
	       (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)))
	      :r (cpl x86) x86))
   (all-translation-governing-addresses
    (create-canonical-address-list
     8
     (page-dir-ptr-table-entry-addr
      (xr :rgf *rdi* x86)
      (pdpt-base-addr (xr :rgf *rdi* x86) x86)))
    x86)))

(defun-nx more-stack-containing-return-address-and-destination-PML4E-no-interfere-p (x86)
  (disjoint-p
   (mv-nth
    1
    (las-to-pas
     (create-canonical-address-list
      8
      (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86)))
     :r (cpl x86) x86))
   (all-translation-governing-addresses
    (create-canonical-address-list 8 (xr :rgf *rsp* x86))
    x86)))

(defun-nx more-destination-PDPTE-and-destination-PML4TE-no-interfere-p (x86)
  (and
   (disjoint-p
    (mv-nth
     1
     (las-to-pas
      (create-canonical-address-list
       8
       (page-dir-ptr-table-entry-addr
	(xr :rgf *rsi* x86)
	(pdpt-base-addr (xr :rgf *rsi* x86) x86)))
      :w (cpl x86) x86))
    (mv-nth
     1
     (las-to-pas
      (create-canonical-address-list
       8
       (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86)))
      :r (cpl x86) x86)))
   (disjoint-p
    (mv-nth
     1
     (las-to-pas
      (create-canonical-address-list
       8
       (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86)))
      :r (cpl x86) x86))
    (all-translation-governing-addresses
     (create-canonical-address-list
      8
      (page-dir-ptr-table-entry-addr
       (xr :rgf *rsi* x86)
       (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
     x86))))


(defun-nx throwaway-hyps-for-source-entries-from-final-state (x86)
  (and
   ;; From source-pml4te-ok-p:
   (disjoint-p
    (mv-nth 1 (las-to-pas
	       (create-canonical-address-list
		8
		(pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)))
	       :r (cpl x86) x86))
    (all-translation-governing-addresses
     (create-canonical-address-list
      8
      (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)))
     x86))

   ;; Derived from destination-PDPTE-and-source-PML4E-no-interfere-p.
   (disjoint-p
    (mv-nth 1 (las-to-pas
	       (create-canonical-address-list
		8
		(page-dir-ptr-table-entry-addr
		 (xr :rgf *rsi* x86)
		 (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
	       :w (cpl x86) x86))
    (all-translation-governing-addresses
     (create-canonical-address-list
      8
      (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)))
     x86))

   ;; Derived from source-PML4TE-and-stack-no-interfere-p:
   (disjoint-p
    (mv-nth 1 (las-to-pas
	       (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86))) :w (cpl x86) x86))
    (mv-nth 1 (las-to-pas
	       (create-canonical-address-list
		8
		(pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)))
	       :r (cpl x86) x86)))))

(defun-nx throwaway-hyps-for-destination-entries-from-final-state (x86)
  (and
   ;; disjoint-p$ issue:
   ;; Derived from destination-PML4TE-and-source-PDPTE-no-interfere-p:
   (disjoint-p
    (mv-nth
     1
     (las-to-pas
      (create-canonical-address-list
       8
       (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86)))
      :r (cpl x86) x86))
    (all-translation-governing-addresses
     (create-canonical-address-list
      8
      (page-dir-ptr-table-entry-addr
       (xr :rgf *rdi* x86)
       (pdpt-base-addr (xr :rgf *rdi* x86) x86)))
     x86))

   ;; disjoint-p$ issue:
   ;; Derived from destination-PML4TE-and-source-PML4TE-no-interfere-p:
   (disjoint-p
    (mv-nth
     1
     (las-to-pas
      (create-canonical-address-list
       8
       (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86)))
      :r (cpl x86) x86))
    (all-translation-governing-addresses
     (create-canonical-address-list
      8
      (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)))
     x86))

   ;; disjoint-p$ issue:
   ;; Derived from destination-PML4TE-and-stack-no-interfere-p:
   (disjoint-p
    (mv-nth
     1
     (las-to-pas
      (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86)))
      :w (cpl x86) x86))
    (mv-nth
     1
     (las-to-pas
      (create-canonical-address-list
       8
       (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86)))
      :r (cpl x86) x86)))

   ;; disjoint-p$ issue:
   ;; Derived from destination-PML4TE-ok-p:
   (disjoint-p
    (mv-nth
     1
     (las-to-pas (create-canonical-address-list
		  8
		  (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86)))
		 :r (cpl x86) x86))
    (all-translation-governing-addresses
     (create-canonical-address-list
      8
      (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86)))
     x86))

   ;; disjoint-p$ issue:
   ;; Derived from destination-PDPTE-and-destination-PML4TE-no-interfere-p:
   (disjoint-p
    (mv-nth
     1
     (las-to-pas
      (create-canonical-address-list
       8
       (page-dir-ptr-table-entry-addr (xr :rgf *rsi* x86)
				      (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
      :w (cpl x86) x86))
    (all-translation-governing-addresses
     (create-canonical-address-list
      8
      (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86)))
     x86))))

;; ======================================================================

;; Get information about paging entries in the final state:

(defthm xlate-equiv-memory-and-pml4-table-base-addr
  (implies (xlate-equiv-memory x86-1 x86-2)
	   (equal (pml4-table-base-addr x86-1)
		  (pml4-table-base-addr x86-2)))
  :hints (("Goal" :in-theory (e/d* (pml4-table-base-addr) ())))
  :rule-classes :congruence)

(defthm pdpt-base-addr-after-mv-nth-2-las-to-pas
  ;; Similar to mv-nth-1-rb-after-mv-nth-2-las-to-pas.
  (implies (and
	    (disjoint-p
	     (mv-nth
	      1
	      (las-to-pas
	       (create-canonical-address-list
		8
		(pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)))
	       :r (cpl x86) (double-rewrite x86)))
	     (all-translation-governing-addresses l-addrs-2 (double-rewrite x86)))
	    (disjoint-p
	     (mv-nth
	      1
	      (las-to-pas
	       (create-canonical-address-list
		8
		(pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)))
	       :r (cpl x86) (double-rewrite x86)))
	     (all-translation-governing-addresses
	      (create-canonical-address-list
	       8
	       (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)))
	      (double-rewrite x86)))
	    (not (xr :programmer-level-mode 0 x86))
	    (canonical-address-listp l-addrs-2))
	   (equal (pdpt-base-addr lin-addr (mv-nth 2 (las-to-pas l-addrs-2 r-w-x-2 cpl-2 x86)))
		  (pdpt-base-addr lin-addr (double-rewrite x86))))
  :hints (("Goal" :in-theory (e/d* (pdpt-base-addr) (force (force))))))

(defthm pdpt-base-addr-after-mv-nth-1-wb
  ;; Similar to rb-wb-disjoint-in-system-level-mode
  (implies (and
	    (disjoint-p
	     (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) (double-rewrite x86)))
	     (mv-nth 1 (las-to-pas
			(create-canonical-address-list
			 8
			 (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)))
			:r (cpl x86) (double-rewrite x86))))
	    (disjoint-p
	     (mv-nth 1 (las-to-pas
			(create-canonical-address-list
			 8
			 (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)))
			:r (cpl x86) (double-rewrite x86)))
	     (all-translation-governing-addresses
	      (strip-cars addr-lst) (double-rewrite x86)))
	    (disjoint-p
	     (mv-nth 1 (las-to-pas
			(create-canonical-address-list
			 8
			 (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)))
			:r (cpl x86) (double-rewrite x86)))
	     (all-translation-governing-addresses
	      (create-canonical-address-list
	       8
	       (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)))
	      (double-rewrite x86)))
	    (disjoint-p
	     (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) (double-rewrite x86)))
	     (all-translation-governing-addresses
	      (create-canonical-address-list
	       8
	       (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)))
	      (double-rewrite x86)))

	    (addr-byte-alistp addr-lst)
	    (not (programmer-level-mode x86))
	    (x86p x86))
	   (equal (pdpt-base-addr lin-addr (mv-nth 1 (wb addr-lst x86)))
		  (pdpt-base-addr lin-addr (double-rewrite x86))))
  :hints (("Goal" :in-theory (e/d* (pdpt-base-addr)
				   (member-p-strip-cars-of-remove-duplicate-keys
				    remove-duplicate-keys
				    force (force))))))

(defthmd pml4-table-base-addr-from-final-state
  (implies (rewire_dst_to_src-effects-preconditions x86)
	   (equal
	    (pml4-table-base-addr (x86-run (rewire_dst_to_src-clk) x86))
	    (pml4-table-base-addr x86)))
  :hints (("Goal"
	   :use ((:instance rewire_dst_to_src-effects))
	   :in-theory (e/d* (pml4-table-base-addr)
			    (rewire_dst_to_src-effects-preconditions-defs)))))

(in-theory (e/d () (pml4-table-base-addr)))

(local
 (defthmd source-pml4-table-entry-from-final-state-helper
   (implies (and (rewire_dst_to_src-effects-preconditions x86)
		 (throwaway-hyps-for-source-entries-from-final-state x86)
		 (more-stack-containing-return-address-and-source-PML4E-no-interfere-p x86)
		 (more-destination-PDPTE-and-source-PML4E-no-interfere-p x86)
		 (more-destination-PML4TE-and-source-PML4TE-no-interfere-p x86)
		 (more-source-PDPTE-and-source-PML4E-no-interfere-p x86))
	    (equal
	     (mv-nth 1
		     (rb (create-canonical-address-list
			  8
			  (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)))
			 :r
			 (x86-run (rewire_dst_to_src-clk) x86)))
	     (mv-nth 1
		     (rb (create-canonical-address-list
			  8
			  (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)))
			 :r x86))))
   :hints (("Goal"
	    :use ((:instance rewire_dst_to_src-effects))
	    :in-theory (e/d* (pml4-table-base-addr-from-final-state
			      disjoint-p-all-translation-governing-addresses-subset-p)
			     (page-dir-ptr-table-entry-addr-to-c-program-optimized-form
			      unsigned-byte-p-52-of-left-shifting-a-40-bit-vector-by-12
			      unsigned-byte-p-of-combine-bytes-and-rb-in-system-level-mode
			      mv-nth-0-las-to-pas-subset-p-with-l-addrs-from-bind-free
			      two-mv-nth-1-las-to-pas-subset-p-disjoint-from-las-to-pas
			      combine-mv-nth-2-las-to-pas-same-r-w-x-when-addresses-in-sequence
			      rewrite-rb-to-rb-alt
			      las-to-pas-values-and-!flgi
			      create-canonical-address-list
			      gather-all-paging-structure-qword-addresses-!flgi
			      subset-p
			      (:meta acl2::mv-nth-cons-meta)
			      r/x-is-irrelevant-for-mv-nth-2-las-to-pas-when-no-errors
			      acl2::loghead-identity
			      mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures
			      mv-nth-2-las-to-pas-system-level-non-marking-mode
			      member-p-canonical-address-listp
			      xr-page-structure-marking-mode-mv-nth-2-las-to-pas
			      right-shift-to-logtail
			      (:rewrite mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs)
			      (:rewrite greater-logbitp-of-unsigned-byte-p . 2)
			      (:rewrite bitops::logand-with-bitmask)
			      (:rewrite xw-xw-intra-simple-field-shadow-writes)
			      (:rewrite x86-run-opener-not-ms-not-zp-n)
			      (:type-prescription acl2::bitmaskp$inline)
			      (:rewrite x86-run-opener-not-ms-not-fault-zp-n)
			      (:definition ms$inline)
			      (:definition fault$inline)
			      (:rewrite gl::nfix-natp)))))))

(local
 (defthmd throwaway-hyps-for-source-entries-from-final-state-lemma
   (implies (rewire_dst_to_src-effects-preconditions x86)
	    (throwaway-hyps-for-source-entries-from-final-state x86))
   :hints (("Goal"
	    :hands-off (disjoint-p)
	    :in-theory (e/d* (disjoint-p$) ())))))

(defthmd source-pml4-table-entry-from-final-state
  (implies (and (rewire_dst_to_src-effects-preconditions x86)
		(more-stack-containing-return-address-and-source-PML4E-no-interfere-p x86)
		(more-destination-PDPTE-and-source-PML4E-no-interfere-p x86)
		(more-destination-PML4TE-and-source-PML4TE-no-interfere-p x86)
		(more-source-PDPTE-and-source-PML4E-no-interfere-p x86))
	   (equal
	    (mv-nth 1
		    (rb (create-canonical-address-list
			 8
			 (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)))
			:r
			(x86-run (rewire_dst_to_src-clk) x86)))
	    (mv-nth 1
		    (rb (create-canonical-address-list
			 8
			 (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)))
			:r x86))))
  :hints (("Goal"
	   :hands-off (disjoint-p)
	   :in-theory (e/d* () (rewire_dst_to_src-effects-preconditions))
	   :use ((:instance source-pml4-table-entry-from-final-state-helper)
		 (:instance throwaway-hyps-for-source-entries-from-final-state-lemma)))))

(defthmd destination-pml4-table-entry-from-final-state-helper
  (implies (and
	    (rewire_dst_to_src-effects-preconditions x86)
	    (throwaway-hyps-for-destination-entries-from-final-state x86)
	    (more-stack-containing-return-address-and-destination-PML4E-no-interfere-p x86)
	    (more-destination-PDPTE-and-destination-PML4TE-no-interfere-p x86))

	   (equal
	    (mv-nth 1
		    (rb (create-canonical-address-list
			 8
			 (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86)))
			:r
			(x86-run (rewire_dst_to_src-clk) x86)))
	    (mv-nth 1
		    (rb (create-canonical-address-list
			 8
			 (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86)))
			:r x86))))
  :hints (("Goal"
	   :use ((:instance rewire_dst_to_src-effects))
	   :in-theory (e/d* (pml4-table-base-addr-from-final-state
			     disjoint-p-all-translation-governing-addresses-subset-p)
			    (rewrite-rb-to-rb-alt
			     las-to-pas-values-and-!flgi
			     create-canonical-address-list
			     gather-all-paging-structure-qword-addresses-!flgi
			     subset-p
			     (:meta acl2::mv-nth-cons-meta)
			     r/x-is-irrelevant-for-mv-nth-2-las-to-pas-when-no-errors
			     acl2::loghead-identity
			     mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures
			     mv-nth-2-las-to-pas-system-level-non-marking-mode
			     member-p-canonical-address-listp
			     xr-page-structure-marking-mode-mv-nth-2-las-to-pas
			     (:rewrite page-dir-ptr-table-entry-addr-to-c-program-optimized-form)
			     (:rewrite unsigned-byte-p-52-of-left-shifting-a-40-bit-vector-by-12)
			     (:rewrite unsigned-byte-p-of-combine-bytes-and-rb-in-system-level-mode)
			     (:rewrite mv-nth-0-las-to-pas-subset-p-with-l-addrs-from-bind-free)
			     (:rewrite two-mv-nth-1-las-to-pas-subset-p-disjoint-from-las-to-pas)
			     (:rewrite right-shift-to-logtail)
			     (:rewrite combine-mv-nth-2-las-to-pas-same-r-w-x-when-addresses-in-sequence)
			     (:definition int-lists-in-seq-p)
			     (:rewrite bitops::loghead-of-ash-same)
			     (:rewrite mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs)
			     (:rewrite greater-logbitp-of-unsigned-byte-p . 2)
			     (:rewrite acl2::cdr-of-append-when-consp)
			     (:type-prescription binary-append)
			     (:rewrite bitops::logand-with-bitmask)
			     (:rewrite
			      int-lists-in-seq-p-and-append-with-create-canonical-address-list-2)
			     (:rewrite acl2::consp-of-append)
			     (:type-prescription int-lists-in-seq-p)
			     (:rewrite int-lists-in-seq-p-and-append)
			     (:rewrite acl2::car-of-append)
			     (:rewrite xw-xw-intra-simple-field-shadow-writes)
			     (:rewrite x86-run-opener-not-ms-not-zp-n)
			     (:rewrite acl2::right-cancellation-for-+)
			     (:type-prescription acl2::bitmaskp$inline)
			     (:rewrite x86-run-opener-not-ms-not-fault-zp-n)
			     (:definition ms$inline)
			     (:definition fault$inline)
			     (:rewrite gl::nfix-natp))))))

(local
 (defthmd throwaway-hyps-for-destination-entries-from-final-state-lemma
   (implies (rewire_dst_to_src-effects-preconditions x86)
	    (throwaway-hyps-for-destination-entries-from-final-state x86))
   :hints (("Goal"
	    :in-theory (e/d* (disjoint-p$) ())
	    :hands-off (disjoint-p)))))

(defthmd destination-pml4-table-entry-from-final-state
  (implies (and (rewire_dst_to_src-effects-preconditions x86)
		(more-stack-containing-return-address-and-destination-PML4E-no-interfere-p x86)
		(more-destination-PDPTE-and-destination-PML4TE-no-interfere-p x86))

	   (equal
	    (mv-nth 1
		    (rb (create-canonical-address-list
			 8
			 (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86)))
			:r
			(x86-run (rewire_dst_to_src-clk) x86)))
	    (mv-nth 1
		    (rb (create-canonical-address-list
			 8
			 (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86)))
			:r x86))))
  :hints (("Goal"
	   :use ((:instance destination-pml4-table-entry-from-final-state-helper)
		 (:instance throwaway-hyps-for-destination-entries-from-final-state-lemma))
	   :in-theory (e/d* ()
			    (rewire_dst_to_src-effects-preconditions)))))

(in-theory (e/d () (pml4-table-entry-addr)))

(defthmd source-pdpt-base-addr-from-final-state-helper
  (implies (and (rewire_dst_to_src-effects-preconditions x86)
		(throwaway-hyps-for-source-entries-from-final-state x86)
		(more-stack-containing-return-address-and-source-PML4E-no-interfere-p x86)
		(more-destination-PDPTE-and-source-PML4E-no-interfere-p x86)
		(more-destination-PML4TE-and-source-PML4TE-no-interfere-p x86)
		(more-source-PDPTE-and-source-PML4E-no-interfere-p x86))
	   (equal
	    (pdpt-base-addr (xr :rgf *rdi* x86) (x86-run (rewire_dst_to_src-clk) x86))
	    (pdpt-base-addr (xr :rgf *rdi* x86) x86)))
  :hints (("Goal"
	   :use ((:instance rewire_dst_to_src-effects))
	   :in-theory (e/d* (pdpt-base-addr
			     pml4-table-base-addr-from-final-state
			     source-pml4-table-entry-from-final-state)
			    (rewire_dst_to_src-effects-preconditions-defs)))))

(defthmd source-pdpt-base-addr-from-final-state
  (implies (and (rewire_dst_to_src-effects-preconditions x86)
		(more-stack-containing-return-address-and-source-PML4E-no-interfere-p x86)
		(more-destination-PDPTE-and-source-PML4E-no-interfere-p x86)
		(more-destination-PML4TE-and-source-PML4TE-no-interfere-p x86)
		(more-source-PDPTE-and-source-PML4E-no-interfere-p x86))
	   (equal
	    (pdpt-base-addr (xr :rgf *rdi* x86) (x86-run (rewire_dst_to_src-clk) x86))
	    (pdpt-base-addr (xr :rgf *rdi* x86) x86)))
  :hints (("Goal"
	   :use ((:instance throwaway-hyps-for-source-entries-from-final-state-lemma)
		 (:instance source-pdpt-base-addr-from-final-state-helper))
	   :in-theory (e/d* ()
			    (rewire_dst_to_src-effects-preconditions-defs)))))

(local
 (defthmd destination-pdpt-base-addr-from-final-state-helper
   (implies (and (rewire_dst_to_src-effects-preconditions x86)
		 (throwaway-hyps-for-destination-entries-from-final-state x86)
		 (more-stack-containing-return-address-and-destination-PML4E-no-interfere-p x86)
		 (more-destination-PDPTE-and-destination-PML4TE-no-interfere-p x86))
	    (equal
	     (pdpt-base-addr (xr :rgf *rsi* x86) (x86-run (rewire_dst_to_src-clk) x86))
	     (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
   :hints (("Goal"
	    :use ((:instance rewire_dst_to_src-effects))
	    :in-theory (e/d* (pdpt-base-addr
			      pml4-table-base-addr-from-final-state
			      destination-pml4-table-entry-from-final-state)
			     (rewire_dst_to_src-effects-preconditions-defs))))))

(defthmd destination-pdpt-base-addr-from-final-state
  (implies (and (rewire_dst_to_src-effects-preconditions x86)
		(more-stack-containing-return-address-and-destination-PML4E-no-interfere-p x86)
		(more-destination-PDPTE-and-destination-PML4TE-no-interfere-p x86))
	   (equal
	    (pdpt-base-addr (xr :rgf *rsi* x86) (x86-run (rewire_dst_to_src-clk) x86))
	    (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
  :hints (("Goal"
	   :use ((:instance destination-pdpt-base-addr-from-final-state-helper)
		 (:instance throwaway-hyps-for-destination-entries-from-final-state-lemma))
	   :in-theory (e/d* ()
			    (rewire_dst_to_src-effects-preconditions-defs)))))

(in-theory (e/d () (pdpt-base-addr)))
;; page-dir-ptr-table-entry-addr is already disabled. Also, we don't
;; need lemmas about page-dir-ptr-table-entry-addr from the final
;; state because page-dir-ptr-table-entry-addr is not defined in terms
;; of x86.

(defthmd source-addresses-from-final-state
  (implies (and (rewire_dst_to_src-effects-preconditions x86)
		;; The physical addresses corresponding to destination
		;; PDPTE are disjoint from the translation-governing
		;; addresses of the source linear addresses.  Note
		;; that this means that the destination PDPTE can't
		;; serve as the PML4TE or PDPTE of the source.
		(disjoint-p
		 (mv-nth
		  1
		  (las-to-pas
		   (create-canonical-address-list
		    8
		    (page-dir-ptr-table-entry-addr
		     (xr :rgf *rsi* x86)
		     (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
		   :w (cpl x86) x86))
		 (all-translation-governing-addresses
		  (create-canonical-address-list *2^30* (xr :rgf *rdi* x86))
		  x86)))

	   (equal
	    (mv-nth 1
		    (las-to-pas
		     (create-canonical-address-list *2^30* (xr :rgf *rdi* x86))
		     :r (cpl x86)
		     (x86-run (rewire_dst_to_src-clk) x86)))
	    (mv-nth 1
		    (las-to-pas
		     (create-canonical-address-list *2^30* (xr :rgf *rdi* x86))
		     :r (cpl x86) x86))))
  :hints (("Goal"
	   :use ((:instance rewire_dst_to_src-effects))
	   :in-theory (e/d* (pml4-table-base-addr-from-final-state
			     source-pml4-table-entry-from-final-state
			     source-pdpt-base-addr-from-final-state)
			    (rewrite-rb-to-rb-alt
			     page-dir-ptr-table-entry-addr-to-c-program-optimized-form
			     unsigned-byte-p-52-of-left-shifting-a-40-bit-vector-by-12
			     unsigned-byte-p-of-combine-bytes-and-rb-in-system-level-mode
			     infer-disjointness-with-all-translation-governing-addresses-from-gather-all-paging-structure-qword-addresses-with-disjoint-p$
			     mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs
			     subset-p
			     (:meta acl2::mv-nth-cons-meta)
			     create-canonical-address-list
			     mv-nth-0-las-to-pas-subset-p-with-l-addrs-from-bind-free
			     acl2::loghead-identity
			     (:rewrite xr-page-structure-marking-mode-mv-nth-2-las-to-pas)
			     (:rewrite mv-nth-2-las-to-pas-system-level-non-marking-mode)
			     (:rewrite combine-mv-nth-2-las-to-pas-same-r-w-x-when-addresses-in-sequence)
			     (:definition int-lists-in-seq-p)
			     (:rewrite two-mv-nth-1-las-to-pas-subset-p-disjoint-from-las-to-pas)
			     (:rewrite subset-p-two-create-canonical-address-lists-general)
			     (:rewrite xr-page-structure-marking-mode-mv-nth-1-wb)
			     (:rewrite canonical-address-p-limits-thm-0)
			     (:rewrite r/x-is-irrelevant-for-mv-nth-2-las-to-pas-when-no-errors)
			     (:rewrite mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures)
			     (:rewrite acl2::cdr-of-append-when-consp)
			     (:rewrite bitops::logand-with-bitmask)
			     (:rewrite greater-logbitp-of-unsigned-byte-p . 2)
			     (:type-prescription binary-append)
			     (:rewrite int-lists-in-seq-p-and-append-with-create-canonical-address-list-2)
			     (:rewrite acl2::consp-of-append)
			     (:type-prescription int-lists-in-seq-p)
			     (:type-prescription subset-p)
			     (:rewrite int-lists-in-seq-p-and-append)
			     (:rewrite acl2::car-of-append)
			     (:rewrite xw-xw-intra-simple-field-shadow-writes)
			     (:rewrite x86-run-opener-not-ms-not-zp-n)
			     (:rewrite acl2::right-cancellation-for-+)
			     (:type-prescription acl2::bitmaskp$inline)
			     (:rewrite x86-run-opener-not-ms-not-fault-zp-n)
			     (:definition ms$inline)
			     (:definition fault$inline)
			     (:rewrite gl::nfix-natp))))))

(defthmd source-data-from-final-state-in-terms-of-rb
  (implies (and (rewire_dst_to_src-effects-preconditions x86)
		;; The physical addresses corresponding to destination
		;; PDPTE are disjoint from the translation-governing
		;; addresses of the source linear addresses.  Note
		;; that this means that the destination PDPTE can't
		;; serve as the PML4TE or PDPTE of the source.
		(disjoint-p
		 (mv-nth
		  1
		  (las-to-pas
		   (create-canonical-address-list
		    8
		    (page-dir-ptr-table-entry-addr
		     (xr :rgf *rsi* x86)
		     (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
		   :w (cpl x86) x86))
		 (all-translation-governing-addresses
		  (create-canonical-address-list *2^30* (xr :rgf *rdi* x86))
		  x86))

		;; The physical addresses corresponding to destination
		;; PDPTE are disjoint from the source physical
		;; addresses.
		(disjoint-p
		 (mv-nth
		  1
		  (las-to-pas
		   (create-canonical-address-list
		    8
		    (page-dir-ptr-table-entry-addr
		     (xr :rgf *rsi* x86)
		     (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
		   :w (cpl x86) x86))
		 (mv-nth 1
			 (las-to-pas (create-canonical-address-list *2^30* (xr :rgf *rdi* x86))
				     :r (cpl x86) x86)))

		;; The source physical addresses are disjoint from the
		;; paging structures.
		(disjoint-p$
		 (mv-nth 1
			 (las-to-pas (create-canonical-address-list *2^30* (xr :rgf *rdi* x86))
				     :r (cpl x86) x86))
		 (open-qword-paddr-list
		  (gather-all-paging-structure-qword-addresses x86)))

		;; The stack is disjoint from the source physical
		;; addresses.
		(disjoint-p
		 (mv-nth
		  1
		  (las-to-pas
		   (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86)))
		   :w (cpl x86) x86))
		 (mv-nth 1
			 (las-to-pas (create-canonical-address-list *2^30* (xr :rgf *rdi* x86))
				     :r (cpl x86) x86))))

	   (equal
	    (mv-nth 1 (rb (create-canonical-address-list *2^30* (xr :rgf *rdi* x86))
			  :r
			  (x86-run (rewire_dst_to_src-clk) x86)))
	    (mv-nth 1 (rb (create-canonical-address-list *2^30* (xr :rgf *rdi* x86))
			  :r x86))))
  :hints (("Goal"
	   :use ((:instance rewire_dst_to_src-effects))
	   :in-theory (e/d*
		       (pml4-table-base-addr-from-final-state
			source-pml4-table-entry-from-final-state
			source-pdpt-base-addr-from-final-state
			source-addresses-from-final-state

			disjoint-p-all-translation-governing-addresses-subset-p)

		       (rewrite-rb-to-rb-alt
			page-dir-ptr-table-entry-addr-to-c-program-optimized-form
			unsigned-byte-p-52-of-left-shifting-a-40-bit-vector-by-12
			unsigned-byte-p-of-combine-bytes-and-rb-in-system-level-mode
			mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs
			subset-p
			(:meta acl2::mv-nth-cons-meta)
			create-canonical-address-list
			mv-nth-0-las-to-pas-subset-p-with-l-addrs-from-bind-free
			acl2::loghead-identity
			(:rewrite xr-page-structure-marking-mode-mv-nth-2-las-to-pas)
			(:rewrite r/x-is-irrelevant-for-mv-nth-2-las-to-pas-when-no-errors)
			(:rewrite mv-nth-2-las-to-pas-system-level-non-marking-mode)
			(:rewrite two-mv-nth-1-las-to-pas-subset-p-disjoint-from-las-to-pas)
			(:rewrite combine-mv-nth-2-las-to-pas-same-r-w-x-when-addresses-in-sequence)
			(:definition int-lists-in-seq-p)
			(:rewrite mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures)
			(:rewrite xr-page-structure-marking-mode-mv-nth-1-wb)
			(:rewrite bitops::logand-with-bitmask)
			(:rewrite acl2::cdr-of-append-when-consp)
			(:rewrite greater-logbitp-of-unsigned-byte-p . 2)
			(:type-prescription binary-append)
			(:rewrite int-lists-in-seq-p-and-append-with-create-canonical-address-list-2)
			(:rewrite acl2::consp-of-append)
			(:type-prescription int-lists-in-seq-p)
			(:rewrite int-lists-in-seq-p-and-append)
			(:rewrite acl2::car-of-append)
			(:rewrite xw-xw-intra-simple-field-shadow-writes)
			(:rewrite x86-run-opener-not-ms-not-zp-n)
			(:type-prescription xlate-equiv-memory)
			(:rewrite acl2::right-cancellation-for-+)
			(:type-prescription acl2::bitmaskp$inline)
			(:rewrite x86-run-opener-not-ms-not-fault-zp-n)
			(:definition ms$inline)
			(:definition fault$inline)
			(:rewrite gl::nfix-natp))))))

(defthmd source-data-from-initial-state-in-terms-of-read-from-physical-memory-and-las-to-pas
  (implies (and
	    (rewire_dst_to_src-effects-preconditions x86)
	    (disjoint-p$
	     (mv-nth
	      1
	      (las-to-pas (create-canonical-address-list *2^30* (xr :rgf *rdi* x86))
			  :r (cpl x86) x86))
	     (open-qword-paddr-list
	      (gather-all-paging-structure-qword-addresses x86))))

	   (equal
	    (mv-nth 1 (rb (create-canonical-address-list *2^30* (xr :rgf *rdi* x86))
			  :r x86))
	    (read-from-physical-memory
	     (mv-nth
	      1
	      (las-to-pas (create-canonical-address-list *2^30* (xr :rgf *rdi* x86)) :r 0 x86))
	     x86)))
  :hints (("Goal"
	   :in-theory (e/d*
		       (rb)
		       (rewrite-rb-to-rb-alt
			page-dir-ptr-table-entry-addr-to-c-program-optimized-form
			unsigned-byte-p-52-of-left-shifting-a-40-bit-vector-by-12
			unsigned-byte-p-of-combine-bytes-and-rb-in-system-level-mode
			mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs
			subset-p
			(:meta acl2::mv-nth-cons-meta)
			create-canonical-address-list
			mv-nth-0-las-to-pas-subset-p-with-l-addrs-from-bind-free
			acl2::loghead-identity)))))

;; In order to prove destination-data-from-final-state-*, I first need
;; las-to-pas-values-1G-pages-and-wb-to-page-dir-ptr-table-entry-addr,
;; all-translation-governing-addresses-1G-pages-and-wb-to-page-dir-ptr-table-entry-addr,
;; and rb-values-1G-pages-and-wb-to-page-dir-ptr-table-entry-addr.

;; ======================================================================

(in-theory (e/d* (rewire_dst_to_src-disable
		  rewire_dst_to_src-disable-more)
		 (unsigned-byte-p
		  signed-byte-p)))

;; ======================================================================

;; Rewriting (combine-bytes (mv-nth 1 (rb ...))) to rm-low-64 if the
;; lin-addr is direct-mapped:

(def-gl-export rb-and-rm-low-64-for-direct-map-helper-1
  :hyp (and (n08p a) (n08p b) (n08p c) (n08p d)
	    (n08p e) (n08p f) (n08p g) (n08p h))
  :concl (equal (logior a (ash b 8)
			(ash (logior c (ash d 8)) 16)
			(ash (logior e (ash (logior f (ash (logior g (ash h 8)) 8)) 8)) 32))
		(logior a
			(ash (logior b
				     (ash (logior c
						  (ash
						   (logior d
							   (ash
							    (logior
							     e
							     (ash
							      (logior
							       f
							       (ash (logior g (ash h 8)) 8))
							      8)) 8)) 8)) 8)) 8)))
  :g-bindings
  (gl::auto-bindings
   (:mix (:nat a 8) (:nat b 8) (:nat c 8) (:nat d 8)
	 (:nat e 8) (:nat f 8) (:nat g 8) (:nat h 8))))

(def-gl-export rb-and-rm-low-64-for-direct-map-helper-2
  :hyp (and (n08p a) (n08p b) (n08p c) (n08p d)
	    (n08p e) (n08p f) (n08p g) (n08p h))
  :concl (equal (loghead
		 64
		 (logior a
			 (ash b 8)
			 (ash (logior c (ash d 8)) 16)
			 (ash (logior e (ash (logior f (ash (logior g (ash h 8)) 8)) 8)) 32)))
		(logior a
			(ash b 8)
			(ash (logior c (ash d 8)) 16)
			(ash (logior e (ash (logior f (ash (logior g (ash h 8)) 8)) 8)) 32)))
  :g-bindings
  (gl::auto-bindings
   (:mix (:nat a 8) (:nat b 8) (:nat c 8) (:nat d 8)
	 (:nat e 8) (:nat f 8) (:nat g 8) (:nat h 8))))

(in-theory (e/d* () (rb-and-rm-low-64-for-direct-map-helper-1
		     rb-and-rm-low-64-for-direct-map-helper-2)))

(defthm rb-and-rm-low-64-for-direct-map
  (implies (and
	    (direct-map-p 8 direct-mapped-addr r-w-x (cpl x86) (double-rewrite x86))
	    ;; The physical addresses corresponding to
	    ;; direct-mapped-addr to (+ 7 direct-mapped-addr) are
	    ;; disjoint from their own translation-governing
	    ;; addresses.
	    (disjoint-p$
	     (mv-nth 1
		     (las-to-pas (create-canonical-address-list 8 direct-mapped-addr)
				 r-w-x (cpl x86)
				 (double-rewrite x86)))
	     (all-translation-governing-addresses
	      (create-canonical-address-list 8 direct-mapped-addr)
	      (double-rewrite x86)))
	    (not
	     (mv-nth 0
		     (las-to-pas (create-canonical-address-list 8 direct-mapped-addr)
				 r-w-x (cpl x86)
				 (double-rewrite x86))))
	    (physical-address-p direct-mapped-addr)
	    (canonical-address-p (+ 7 direct-mapped-addr))
	    (not (programmer-level-mode x86))
	    (x86p x86))
	   (equal (combine-bytes
		   (mv-nth
		    1
		    (rb (create-canonical-address-list 8 direct-mapped-addr) r-w-x x86)))
		  (rm-low-64 direct-mapped-addr (double-rewrite x86))))
  :hints (("Goal"
	   :use ((:instance rewrite-read-from-physical-memory-to-rm-low-64
			    (p-addrs (addr-range 8 direct-mapped-addr))
			    (index direct-mapped-addr)
			    (x86 x86))
		 (:instance rb-and-rm-low-64-for-direct-map-helper-2
			    (a (xr :mem      direct-mapped-addr  x86))
			    (b (xr :mem (+ 1 direct-mapped-addr) x86))
			    (c (xr :mem (+ 2 direct-mapped-addr) x86))
			    (d (xr :mem (+ 3 direct-mapped-addr) x86))
			    (e (xr :mem (+ 4 direct-mapped-addr) x86))
			    (f (xr :mem (+ 5 direct-mapped-addr) x86))
			    (g (xr :mem (+ 6 direct-mapped-addr) x86))
			    (h (xr :mem (+ 7 direct-mapped-addr) x86))))
	   :in-theory (e/d* (rb
			     disjoint-p$
			     direct-map-p
			     rm-low-64
			     rm-low-32
			     n08p
			     unsigned-byte-p
			     signed-byte-p)
			    (rb-and-rm-low-64-for-direct-map-helper-1
			     rb-and-rm-low-64-for-direct-map-helper-2
			     xlate-equiv-memory-and-xr-mem-from-rest-of-memory
			     bitops::loghead-of-logior
			     (:linear bitops::logior-<-0-linear-2)
			     (:linear ash-monotone-2)
			     (:rewrite bitops::ash-<-0)
			     (:rewrite acl2::ash-0)
			     (:rewrite acl2::zip-open)
			     (:linear <=-logior)
			     (:linear bitops::logior->=-0-linear)
			     (:linear bitops::logior-<-0-linear-1))))))

;; ======================================================================

;; We now compute the physical address corresponding to (+ n lin-addr)
;; that is returned by ia32e-la-to-pa, given that (+ n lin-addr) lies
;; in the same 1G page as lin-addr.  We then generalize this result to
;; las-to-pas (from ia32e-la-to-pa).

(def-gl-export same-pml4-table-entry-addr-for-n-+-lin-addrs
  :hyp (and (physical-address-p pml4-table-base-addr)
	    (canonical-address-p lin-addr)
	    (unsigned-byte-p 30 n)
	    ;; 1G aligned linear address
	    (equal (loghead 30 lin-addr) 0))
  :concl (equal (pml4-table-entry-addr (+ n lin-addr) pml4-table-base-addr)
		(pml4-table-entry-addr lin-addr pml4-table-base-addr))
  :g-bindings
  (gl::auto-bindings
   (:mix (:nat pml4-table-base-addr 64) (:nat lin-addr 64) (:nat n 64))))

(def-gl-export same-pdp-table-entry-addr-for-n-+-lin-addrs
  :hyp (and (unsigned-byte-p 30 n)
	    (physical-address-p pdpt-base-addr)
	    (canonical-address-p lin-addr)
	    ;; 1G aligned linear address
	    (equal (loghead 30 lin-addr) 0))
  :concl (equal (page-dir-ptr-table-entry-addr
		 (+ n lin-addr) pdpt-base-addr)
		(page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
  :g-bindings
  (gl::auto-bindings
   (:mix (:nat pdpt-base-addr 64) (:nat lin-addr 64) (:nat n 64))))

(def-gl-export loghead-30-of-1G-aligned-lin-addr-+-n-1
  :hyp (and (canonical-address-p lin-addr)
	    (canonical-address-p (+ n lin-addr))
	    (equal (loghead 30 lin-addr) 0)
	    (unsigned-byte-p 30 n))
  :concl (equal (loghead 30 (+ n lin-addr)) n)
  :g-bindings (gl::auto-bindings (:mix (:nat lin-addr 64) (:nat n 64))))

(def-gl-export loghead-30-of-1G-aligned-lin-addr-+-n-2
  :hyp (and (equal (loghead 30 (+ n lin-addr)) n)
	    (canonical-address-p (+ n lin-addr))
	    (canonical-address-p lin-addr)
	    (unsigned-byte-p 30 n))
  :concl (equal (loghead 30 lin-addr) 0)
  :g-bindings (gl::auto-bindings (:mix (:nat lin-addr 64) (:nat n 64))))

(def-gl-export logior-to-+-for-ash-x-30
  :hyp (and (unsigned-byte-p 22 x)
	    (unsigned-byte-p 30 n))
  :concl (equal (logior n (ash x 30)) (+ n (ash x 30)))
  :g-bindings
  (gl::auto-bindings (:mix (:nat n 64) (:nat x 64))))

(defthmd ia32e-la-to-pa-page-dir-ptr-table-values-for-same-1G-page
  ;; This lemma returns the flg and phy-addr values output by
  ;; ia32e-la-to-pa-page-dir-ptr-table for the linear address (+ n
  ;; lin-addr), where this address lies in the same 1G page as
  ;; lin-addr.
  (implies
   (and
    (equal page-dir-ptr-table-entry
	   (combine-bytes
	    (mv-nth 1
		    (rb (create-canonical-address-list
			 8
			 (page-dir-ptr-table-entry-addr lin-addr base-addr))
			r-w-x x86))))
    (equal cpl (cpl x86))
    ;; PDPTE is direct-mapped.
    (direct-map-p 8
		  (page-dir-ptr-table-entry-addr lin-addr base-addr)
		  r-w-x cpl (double-rewrite x86))
    (not
     (mv-nth
      0
      (las-to-pas (create-canonical-address-list
		   8
		   (page-dir-ptr-table-entry-addr lin-addr base-addr))
		  r-w-x cpl x86)))
    (disjoint-p$
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list
	8
	(page-dir-ptr-table-entry-addr lin-addr base-addr))
       r-w-x cpl x86))
     (all-translation-governing-addresses
      (create-canonical-address-list
       8 (page-dir-ptr-table-entry-addr lin-addr base-addr))
      x86))
    (not
     (mv-nth
      0
      (ia32e-la-to-pa-page-dir-ptr-table
       lin-addr base-addr u/s-acc r/w-acc x/d-acc
       wp smep smap ac nxe r-w-x cpl x86)))

    (equal (page-size page-dir-ptr-table-entry) 1)
    (canonical-address-p (+ 7 (page-dir-ptr-table-entry-addr lin-addr base-addr)))
    (canonical-address-p lin-addr)
    (canonical-address-p (+ n lin-addr))
    (equal (loghead 30 (+ n lin-addr)) n)
    (unsigned-byte-p 30 n)
    (physical-address-p base-addr)
    (equal (loghead 12 base-addr) 0)
    (x86p x86))
   (and
    (equal (mv-nth 0
		   (ia32e-la-to-pa-page-dir-ptr-table
		    (+ n lin-addr) base-addr u/s-acc r/w-acc x/d-acc
		    wp smep smap ac nxe r-w-x cpl x86))
	   nil)
    (equal (mv-nth 1
		   (ia32e-la-to-pa-page-dir-ptr-table
		    (+ n lin-addr) base-addr u/s-acc r/w-acc x/d-acc
		    wp smep smap ac nxe r-w-x cpl x86))
	   (+ n
	      (ash
	       (loghead 22 (logtail
			    30
			    (rm-low-64 (page-dir-ptr-table-entry-addr lin-addr base-addr) x86)))
	       30)))))
  :hints (("Goal" :in-theory (e/d* (ia32e-la-to-pa-page-dir-ptr-table)
				   (commutativity-of-+
				    not
				    page-dir-ptr-table-entry-addr-to-c-program-optimized-form
				    bitops::logand-with-negated-bitmask)))))

(defthmd ia32e-la-to-pa-pml4-table-values-for-same-1G-page
  ;; This lemma returns the flg and phy-addr values output by
  ;; ia32e-la-to-pa-pml4-table for the linear address (+ n lin-addr),
  ;; where this address lies in the same 1G page as lin-addr.
  (implies
   (and
    (equal cpl (cpl x86))
    (equal pml4-table-base-addr (pml4-table-base-addr x86))
    (equal pml4-table-entry-addr (pml4-table-entry-addr lin-addr pml4-table-base-addr))
    (equal pml4-table-entry
	   (combine-bytes
	    (mv-nth 1
		    (rb (create-canonical-address-list 8 pml4-table-entry-addr)
			:r x86))))
    (equal pdpt-base-addr (pdpt-base-addr lin-addr x86))
    (equal page-dir-ptr-table-entry-addr
	   (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
    (equal
     page-dir-ptr-table-entry
     (combine-bytes
      (mv-nth
       1
       (rb (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
	   :r x86))))
    (direct-map-p 8 pml4-table-entry-addr :r cpl (double-rewrite x86))
    (not
     (mv-nth
      0
      (las-to-pas (create-canonical-address-list 8 pml4-table-entry-addr)
		  :r cpl x86)))
    (disjoint-p$
     (mv-nth
      1
      (las-to-pas (create-canonical-address-list 8 pml4-table-entry-addr)
		  :r cpl x86))
     (all-translation-governing-addresses
      (create-canonical-address-list 8 pml4-table-entry-addr)
      x86))
    (direct-map-p 8 page-dir-ptr-table-entry-addr :r cpl (double-rewrite x86))
    (not
     (mv-nth
      0
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r cpl x86)))
    (disjoint-p$
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r cpl x86))
     (all-translation-governing-addresses
      (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
      x86))

    (disjoint-p (addr-range 8 pml4-table-entry-addr)
		(addr-range 8 page-dir-ptr-table-entry-addr))
    (equal (page-size page-dir-ptr-table-entry) 1)

    (not (mv-nth 0
		 (ia32e-la-to-pa-pml4-table
		  lin-addr pml4-table-base-addr wp smep smap ac nxe :r cpl x86)))

    (canonical-address-p (+ 7 pml4-table-entry-addr))
    (canonical-address-p (+ 7 page-dir-ptr-table-entry-addr))
    (canonical-address-p lin-addr)
    (canonical-address-p (+ n lin-addr))
    (equal (loghead 30 (+ n lin-addr)) n)
    (unsigned-byte-p 30 n)
    (physical-address-p pml4-table-base-addr)
    (equal (loghead 12 pml4-table-base-addr) 0)
    (x86p x86))
   (and
    (equal (mv-nth 0
		   (ia32e-la-to-pa-pml4-table (+ n lin-addr) pml4-table-base-addr
					      wp smep smap ac nxe :r cpl x86))
	   nil)
    (equal (mv-nth 1
		   (ia32e-la-to-pa-pml4-table (+ n lin-addr) pml4-table-base-addr
					      wp smep smap ac nxe :r cpl x86))
	   (+ n (ash (loghead 22 (logtail 30 (rm-low-64 page-dir-ptr-table-entry-addr x86)))
		     30)))))
  :hints (("Goal"
	   :in-theory (e/d* (ia32e-la-to-pa-pml4-table
			     pdpt-base-addr
			     ia32e-la-to-pa-page-dir-ptr-table-values-for-same-1G-page)
			    (commutativity-of-+
			     not
			     pml4-table-entry-addr-to-c-program-optimized-form
			     bitops::logand-with-negated-bitmask)))))

(defthmd ia32e-la-to-pa-values-for-same-1G-page
  ;; This lemma returns the flg and phy-addr values output by
  ;; ia32e-la-to-pa for the linear address (+ n lin-addr), where this
  ;; address lies in the same 1G page as lin-addr.
  (implies
   (and
    (equal cpl (cpl x86))
    (equal pml4-table-base-addr (pml4-table-base-addr x86))
    (equal pml4-table-entry-addr (pml4-table-entry-addr lin-addr pml4-table-base-addr))
    (equal pml4-table-entry
	   (combine-bytes
	    (mv-nth 1
		    (rb (create-canonical-address-list 8 pml4-table-entry-addr)
			:r x86))))
    (equal pdpt-base-addr (pdpt-base-addr lin-addr x86))
    (equal page-dir-ptr-table-entry-addr
	   (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
    (equal
     page-dir-ptr-table-entry
     (combine-bytes
      (mv-nth
       1
       (rb (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
	   :r x86))))
    (direct-map-p 8 pml4-table-entry-addr :r cpl (double-rewrite x86))
    (not
     (mv-nth
      0
      (las-to-pas (create-canonical-address-list 8 pml4-table-entry-addr)
		  :r cpl x86)))
    (disjoint-p$
     (mv-nth
      1
      (las-to-pas (create-canonical-address-list 8 pml4-table-entry-addr)
		  :r cpl x86))
     (all-translation-governing-addresses
      (create-canonical-address-list 8 pml4-table-entry-addr)
      x86))
    (direct-map-p 8 page-dir-ptr-table-entry-addr :r cpl (double-rewrite x86))
    (not
     (mv-nth
      0
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r cpl x86)))
    (disjoint-p$
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r cpl x86))
     (all-translation-governing-addresses
      (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
      x86))

    (disjoint-p$
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r cpl (double-rewrite x86)))
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 pml4-table-entry-addr)
       :r cpl (double-rewrite x86))))
    ;; (disjoint-p (addr-range 8 pml4-table-entry-addr)
    ;;             (addr-range 8 page-dir-ptr-table-entry-addr))
    (equal (page-size page-dir-ptr-table-entry) 1)

    (not (mv-nth 0 (ia32e-la-to-pa lin-addr :r cpl x86)))

    (canonical-address-p (+ 7 pml4-table-entry-addr))
    (canonical-address-p (+ 7 page-dir-ptr-table-entry-addr))
    (canonical-address-p lin-addr)
    (canonical-address-p (+ n lin-addr))
    (equal (loghead 30 (+ n lin-addr)) n)
    (unsigned-byte-p 30 n)
    (x86p x86))
   (and
    (equal (mv-nth 0 (ia32e-la-to-pa (+ n lin-addr) :r cpl x86)) nil)
    (equal (mv-nth 1 (ia32e-la-to-pa (+ n lin-addr) :r cpl x86))
	   (+ n (ash (loghead 22 (logtail 30 (rm-low-64 page-dir-ptr-table-entry-addr x86)))
		     30)))))
  :hints (("Goal"
	   :in-theory (e/d* (ia32e-la-to-pa
			     disjoint-p$
			     direct-map-p
			     pdpt-base-addr
			     pml4-table-base-addr
			     ia32e-la-to-pa-pml4-table-values-for-same-1G-page)
			    (commutativity-of-+
			     subset-p
			     (:linear acl2::loghead-upper-bound)
			     unsigned-byte-p-of-logtail
			     member-p
			     member-p-canonical-address-listp
			     unsigned-byte-p-of-logtail
			     mv-nth-0-las-to-pas-subset-p
			     not
			     pml4-table-entry-addr-to-c-program-optimized-form
			     bitops::logand-with-negated-bitmask)))))

;; Now generalizing ia32e-la-to-pa-values-for-same-1G-page to
;; las-to-pas:

(define create-canonical-address-list-alt (iteration count lin-addr)
  :enabled t
  :measure (nfix (- count iteration))
  :guard (and (natp count)
	      (natp iteration)
	      (<= iteration count)
	      (integerp lin-addr))
  :long "An alternative way of creating canonical address lists, this
  function also gives a different induction scheme that may be
  preferable to the one suggested by @(see
  create-canonical-address-list)"
  (if (zp (- count iteration))
      nil
    (if (canonical-address-p (+ iteration lin-addr))
	(cons
	 (+ iteration lin-addr)
	 (create-canonical-address-list-alt (+ 1 iteration) count lin-addr))
      nil))
  ///
  (defthmd create-canonical-address-list-alt-is-create-canonical-address-list
    (equal (create-canonical-address-list-alt iteration count lin-addr)
	   (create-canonical-address-list (- count iteration) (+ iteration lin-addr)))))

(def-gl-export open-mv-nth-0-las-to-pas-for-same-1G-page-general-1
  :hyp (and (< iteration m)
	    (canonical-address-p lin-addr)
	    (canonical-address-p (+ -1 lin-addr m))
	    (integerp m)
	    (<= m *2^30*)
	    (natp iteration)
	    (equal (loghead 30 lin-addr) 0))
  :concl (equal (loghead 30 (+ iteration lin-addr)) iteration)
  :g-bindings (gl::auto-bindings (:mix (:nat lin-addr 64) (:nat iteration 64) (:nat m 64))))

(def-gl-export open-mv-nth-0-las-to-pas-for-same-1G-page-general-2
  :hyp (and (< iteration m)
	    (integerp m)
	    (<= m *2^30*)
	    (natp iteration))
  :concl (unsigned-byte-p 30 iteration)
  :g-bindings (gl::auto-bindings (:mix (:nat iteration 64) (:nat m 64))))

(def-gl-export open-mv-nth-1-las-to-pas-for-same-1G-page-general-1
  :hyp (and (< iteration m)
	    (canonical-address-p lin-addr)
	    (canonical-address-p (+ -1 lin-addr m))
	    (integerp m)
	    (<= m 1073741824)
	    (natp iteration)
	    (equal (loghead 30 lin-addr) 0))
  :concl (canonical-address-p (+ iteration lin-addr))
  :g-bindings (gl::auto-bindings (:mix (:nat lin-addr 64) (:nat iteration 64) (:nat m 64))))

(def-gl-export open-mv-nth-1-las-to-pas-for-same-1G-page-general-2
  :hyp (and (canonical-address-p lin-addr)
	    (equal (loghead 30 lin-addr) 0))
  :concl
  ;; (canonical-address-p (+ -1 *2^30* lin-addr))
  (canonical-address-p (+ 1073741823 lin-addr))
  :g-bindings (gl::auto-bindings (:nat lin-addr 64)))

(defthmd las-to-pas-values-for-same-1G-page-general
  (implies
   (and
    (equal cpl (cpl x86))
    (equal pml4-table-base-addr (pml4-table-base-addr x86))
    (equal pml4-table-entry-addr (pml4-table-entry-addr lin-addr pml4-table-base-addr))
    (equal pml4-table-entry
	   (combine-bytes
	    (mv-nth 1
		    (rb (create-canonical-address-list 8 pml4-table-entry-addr)
			:r x86))))
    (equal pdpt-base-addr (pdpt-base-addr lin-addr x86))
    (equal page-dir-ptr-table-entry-addr
	   (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
    (equal
     page-dir-ptr-table-entry
     (combine-bytes
      (mv-nth
       1
       (rb (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
	   :r x86))))
    (direct-map-p 8 pml4-table-entry-addr :r cpl (double-rewrite x86))
    (not
     (mv-nth
      0
      (las-to-pas (create-canonical-address-list 8 pml4-table-entry-addr)
		  :r cpl x86)))
    (disjoint-p$
     (mv-nth
      1
      (las-to-pas (create-canonical-address-list 8 pml4-table-entry-addr)
		  :r cpl x86))
     (all-translation-governing-addresses
      (create-canonical-address-list 8 pml4-table-entry-addr)
      x86))
    (direct-map-p 8 page-dir-ptr-table-entry-addr :r cpl (double-rewrite x86))
    (not
     (mv-nth
      0
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r cpl x86)))
    (disjoint-p$
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r cpl x86))
     (all-translation-governing-addresses
      (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
      x86))

    ;; (disjoint-p (addr-range 8 pml4-table-entry-addr)
    ;;             (addr-range 8 page-dir-ptr-table-entry-addr))
    (disjoint-p$
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r cpl (double-rewrite x86)))
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 pml4-table-entry-addr)
       :r cpl (double-rewrite x86))))
    (equal (page-size page-dir-ptr-table-entry) 1)

    (not (mv-nth 0 (ia32e-la-to-pa lin-addr :r cpl x86)))

    (canonical-address-p (+ 7 pml4-table-entry-addr))
    (canonical-address-p (+ 7 page-dir-ptr-table-entry-addr))

    (canonical-address-p lin-addr)
    (canonical-address-p (+ -1 lin-addr m))
    (natp m)
    (<= m *2^30*)
    (natp iteration)
    (equal (loghead 30 lin-addr) 0)
    (x86p x86))
   (and
    (equal (mv-nth 0 (las-to-pas
		      (create-canonical-address-list-alt iteration m lin-addr)
		      :r cpl x86))
	   nil)
    (equal (mv-nth 1 (las-to-pas
		      (create-canonical-address-list-alt iteration m lin-addr)
		      :r cpl x86))
	   (addr-range
	    (+ (- iteration) m)
	    (+ iteration
	       (ash (loghead 22 (logtail 30 (rm-low-64 page-dir-ptr-table-entry-addr x86)))
		    30))))))
  :hints (("Goal"
	   :induct (create-canonical-address-list-alt iteration m lin-addr)
	   :in-theory (e/d* (las-to-pas
			     ia32e-la-to-pa-values-for-same-1G-page
			     open-mv-nth-0-las-to-pas-for-same-1G-page-general-1
			     open-mv-nth-0-las-to-pas-for-same-1G-page-general-2
			     open-mv-nth-1-las-to-pas-for-same-1G-page-general-1)
			    (not
			     pml4-table-base-addr
			     pml4-table-entry-addr
			     page-dir-ptr-table-entry-addr
			     page-dir-ptr-table-entry-addr-to-c-program-optimized-form)))))

(defthmd las-to-pas-values-for-same-1G-page
  (implies
   (and
    (equal cpl (cpl x86))
    (equal pml4-table-base-addr (pml4-table-base-addr x86))
    (equal pml4-table-entry-addr (pml4-table-entry-addr lin-addr pml4-table-base-addr))
    (equal pml4-table-entry
	   (combine-bytes
	    (mv-nth 1
		    (rb (create-canonical-address-list 8 pml4-table-entry-addr)
			:r x86))))
    (equal pdpt-base-addr (pdpt-base-addr lin-addr x86))
    (equal page-dir-ptr-table-entry-addr
	   (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
    (equal
     page-dir-ptr-table-entry
     (combine-bytes
      (mv-nth
       1
       (rb (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
	   :r x86))))
    (direct-map-p 8 pml4-table-entry-addr :r cpl (double-rewrite x86))
    (not
     (mv-nth
      0
      (las-to-pas (create-canonical-address-list 8 pml4-table-entry-addr)
		  :r cpl x86)))
    (disjoint-p$
     (mv-nth
      1
      (las-to-pas (create-canonical-address-list 8 pml4-table-entry-addr)
		  :r cpl x86))
     (all-translation-governing-addresses
      (create-canonical-address-list 8 pml4-table-entry-addr)
      x86))
    (direct-map-p 8 page-dir-ptr-table-entry-addr :r cpl (double-rewrite x86))
    (not
     (mv-nth
      0
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r cpl x86)))
    (disjoint-p$
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r cpl x86))
     (all-translation-governing-addresses
      (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
      x86))

    ;; (disjoint-p (addr-range 8 pml4-table-entry-addr)
    ;;             (addr-range 8 page-dir-ptr-table-entry-addr))
    (disjoint-p$
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r cpl (double-rewrite x86)))
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 pml4-table-entry-addr)
       :r cpl (double-rewrite x86))))
    (equal (page-size page-dir-ptr-table-entry) 1)

    (not (mv-nth 0 (ia32e-la-to-pa lin-addr :r cpl x86)))

    (canonical-address-p (+ 7 pml4-table-entry-addr))
    (canonical-address-p (+ 7 page-dir-ptr-table-entry-addr))

    (canonical-address-p lin-addr)
    (equal (loghead 30 lin-addr) 0)
    (x86p x86))
   (and
    (equal (mv-nth 0 (las-to-pas
		      (create-canonical-address-list *2^30* lin-addr)
		      :r cpl x86))
	   nil)
    (equal (mv-nth 1 (las-to-pas
		      (create-canonical-address-list *2^30* lin-addr)
		      :r cpl x86))
	   (addr-range
	    *2^30*
	    (ash (loghead 22 (logtail 30 (rm-low-64 page-dir-ptr-table-entry-addr x86)))
		 30)))))
  :hints (("Goal"
	   :use ((:instance las-to-pas-values-for-same-1G-page-general
			    (iteration 0)
			    (m *2^30*)))
	   :in-theory (e/d* (create-canonical-address-list-alt-is-create-canonical-address-list)
			    (not
			     pml4-table-base-addr
			     pml4-table-entry-addr
			     page-dir-ptr-table-entry-addr
			     page-dir-ptr-table-entry-addr-to-c-program-optimized-form)))))

;; ======================================================================

;; Begin proof of las-to-pas-values-1G-pages-and-wb-to-page-dir-ptr-table-entry-addr:
;; Reading the new mapping (i.e., phy-addr) of a lin-addr, given that
;; its PDPTE has been modified:

(defthmd ia32e-la-to-pa-page-dir-ptr-table-values-1G-pages-and-write-to-page-dir-ptr-table-entry-addr
  ;; Given a 1G page, ia32e-la-to-pa-page-dir-ptr-table returns the
  ;; physical address corresponding to lin-addr after the PDPTE
  ;; corresponding to this lin-addr has been modified --- the new
  ;; PDPTE is (combine-bytes bytes).
  (implies (and
	    (equal p-addrs
		   (addr-range 8 (page-dir-ptr-table-entry-addr lin-addr base-addr)))
	    (equal page-dir-ptr-table-entry
		   (combine-bytes
		    (mv-nth 1
			    (rb (create-canonical-address-list
				 8 (page-dir-ptr-table-entry-addr lin-addr base-addr))
				r-w-x x86))))
	    (equal cpl (cpl x86))

	    ;; PDPTE is direct mapped.
	    (direct-map-p
	     8 (page-dir-ptr-table-entry-addr lin-addr base-addr) r-w-x cpl (double-rewrite x86))
	    (not
	     (mv-nth
	      0
	      (las-to-pas (create-canonical-address-list
			   8 (page-dir-ptr-table-entry-addr lin-addr base-addr))
			  r-w-x cpl x86)))
	    (disjoint-p$
	     (mv-nth
	      1
	      (las-to-pas (create-canonical-address-list
			   8 (page-dir-ptr-table-entry-addr lin-addr base-addr))
			  r-w-x cpl x86))
	     (all-translation-governing-addresses
	      (create-canonical-address-list
	       8 (page-dir-ptr-table-entry-addr lin-addr base-addr))
	      x86))

	    (not
	     (mv-nth
	      0
	      (ia32e-la-to-pa-page-dir-ptr-table
	       lin-addr base-addr u/s-acc r/w-acc x/d-acc
	       wp smep smap ac nxe r-w-x cpl x86)))

	    (equal (page-present page-dir-ptr-table-entry)
		   (page-present (combine-bytes bytes)))
	    (equal (page-read-write page-dir-ptr-table-entry)
		   (page-read-write (combine-bytes bytes)))
	    (equal (page-user-supervisor page-dir-ptr-table-entry)
		   (page-user-supervisor (combine-bytes bytes)))
	    (equal (page-execute-disable page-dir-ptr-table-entry)
		   (page-execute-disable (combine-bytes bytes)))
	    (equal (page-size page-dir-ptr-table-entry)
		   (page-size (combine-bytes bytes)))
	    (equal (page-size page-dir-ptr-table-entry) 1)
	    (equal (part-select page-dir-ptr-table-entry :low 13 :high 29)
		   (part-select (combine-bytes bytes) :low 13 :high 29))

	    (equal (len bytes) (len p-addrs))
	    (byte-listp bytes)
	    (canonical-address-p
	     (+ 7 (page-dir-ptr-table-entry-addr lin-addr base-addr)))
	    (canonical-address-p lin-addr)
	    (physical-address-p base-addr)
	    (equal (loghead 12 base-addr) 0)
	    (x86p x86))
	   (and (equal
		 (mv-nth 0 (ia32e-la-to-pa-page-dir-ptr-table
			    lin-addr base-addr u/s-acc r/w-acc x/d-acc
			    wp smep smap ac nxe r-w-x cpl
			    (write-to-physical-memory p-addrs bytes x86)))
		 nil)
		(equal (mv-nth 1 (ia32e-la-to-pa-page-dir-ptr-table
				  lin-addr base-addr u/s-acc r/w-acc x/d-acc
				  wp smep smap ac nxe r-w-x cpl
				  (write-to-physical-memory p-addrs bytes x86)))
		       (logior (loghead 30 lin-addr)
			       (ash (loghead 22 (logtail 30 (combine-bytes bytes))) 30)))))
  :hints (("Goal"
	   :do-not-induct t
	   :use ((:instance rewrite-wm-low-64-to-write-to-physical-memory
			    (index (page-dir-ptr-table-entry-addr lin-addr base-addr)))
		 (:instance mv-nth-0-paging-entry-no-page-fault-p-and-similar-entries
			    (structure-type 2)
			    (u/s-acc (logand u/s-acc
					     (page-user-supervisor (combine-bytes bytes))))
			    (r/w-acc
			     (logand r/w-acc
				     (page-read-write (combine-bytes bytes))))
			    (x/d-acc (logand x/d-acc
					     (page-execute-disable (combine-bytes bytes))))
			    (ignored 0)
			    (cpl (cpl x86))
			    (entry-1 (combine-bytes
				      (mv-nth 1
					      (rb (create-canonical-address-list
						   8
						   (page-dir-ptr-table-entry-addr lin-addr base-addr))
						  r-w-x x86))))
			    (entry-2 (combine-bytes bytes))))
	   :in-theory (e/d* (disjoint-p
			     member-p
			     ia32e-la-to-pa-page-dir-ptr-table
			     byte-ify-and-combine-bytes)
			    (mv-nth-0-paging-entry-no-page-fault-p-and-similar-entries
			     page-dir-ptr-table-entry-addr-to-c-program-optimized-form
			     wb
			     bitops::logand-with-negated-bitmask
			     (:meta acl2::mv-nth-cons-meta)
			     force (force))))))

(defthmd ia32e-la-to-pa-pml4-table-values-1G-pages-and-write-to-page-dir-ptr-table-entry-addr
  ;; Given a 1G page, ia32e-la-to-pa-pml4-table returns the physical
  ;; address corresponding to lin-addr after the PDPTE corresponding
  ;; to this lin-addr has been modified --- the new PDPTE is
  ;; (combine-bytes bytes).

  ;; Note: I've switched to using :r here instead of r-w-x since
  ;; pdpt-base-addr is defined in terms of :r.  I should probably add
  ;; r-w-x as an argument to this function.
  (implies
   (and
    (equal pml4-table-base-addr (pml4-table-base-addr x86))
    (equal page-dir-ptr-table-entry-addr
	   (page-dir-ptr-table-entry-addr lin-addr (pdpt-base-addr lin-addr x86)))
    (equal p-addrs (addr-range 8 page-dir-ptr-table-entry-addr))
    (equal page-dir-ptr-table-entry
	   (combine-bytes
	    (mv-nth 1 (rb (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
			  :r x86))))
    (equal cpl (cpl x86))

    ;; PML4TE is direct-mapped.
    (direct-map-p
     8 (pml4-table-entry-addr lin-addr pml4-table-base-addr) :r cpl (double-rewrite x86))
    (not
     (mv-nth
      0
      (las-to-pas
       (create-canonical-address-list 8 (pml4-table-entry-addr lin-addr pml4-table-base-addr))
       :r cpl x86)))
    (disjoint-p$
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 (pml4-table-entry-addr lin-addr pml4-table-base-addr))
       :r cpl x86))
     (all-translation-governing-addresses
      (create-canonical-address-list 8 (pml4-table-entry-addr lin-addr pml4-table-base-addr))
      x86))

    ;; PDPTE is direct-mapped.
    (direct-map-p
     8 page-dir-ptr-table-entry-addr :r cpl (double-rewrite x86))
    (not
     (mv-nth
      0
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r cpl x86)))
    (disjoint-p$
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r cpl x86))
     (all-translation-governing-addresses
      (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
      x86))

    ;; Physical addresses of PML4TE and PDPTE are disjoint.
    (disjoint-p (addr-range 8 (pml4-table-entry-addr lin-addr pml4-table-base-addr))
		(addr-range 8 page-dir-ptr-table-entry-addr))

    (not (mv-nth 0
		 (ia32e-la-to-pa-pml4-table
		  lin-addr pml4-table-base-addr wp smep smap ac nxe :r cpl x86)))

    (equal (page-present page-dir-ptr-table-entry)
	   (page-present (combine-bytes bytes)))
    (equal (page-read-write page-dir-ptr-table-entry)
	   (page-read-write (combine-bytes bytes)))
    (equal (page-user-supervisor page-dir-ptr-table-entry)
	   (page-user-supervisor (combine-bytes bytes)))
    (equal (page-execute-disable page-dir-ptr-table-entry)
	   (page-execute-disable (combine-bytes bytes)))
    (equal (page-size page-dir-ptr-table-entry)
	   (page-size (combine-bytes bytes)))
    (equal (page-size page-dir-ptr-table-entry) 1)
    (equal (part-select page-dir-ptr-table-entry :low 13 :high 29)
	   (part-select (combine-bytes bytes) :low 13 :high 29))

    (equal (len bytes) (len p-addrs))
    (byte-listp bytes)
    (canonical-address-p (+ 7 (pml4-table-entry-addr lin-addr pml4-table-base-addr)))
    (canonical-address-p (+ 7 page-dir-ptr-table-entry-addr))
    (canonical-address-p lin-addr)
    (physical-address-p pml4-table-base-addr)
    (equal (loghead 12 pml4-table-base-addr) 0)
    (x86p x86))
   (and
    (equal
     (mv-nth 0
	     (ia32e-la-to-pa-pml4-table
	      lin-addr pml4-table-base-addr wp smep smap ac nxe :r cpl
	      (write-to-physical-memory p-addrs bytes x86)))
     nil)
    (equal
     (mv-nth 1
	     (ia32e-la-to-pa-pml4-table
	      lin-addr pml4-table-base-addr wp smep smap ac nxe :r cpl
	      (write-to-physical-memory p-addrs bytes x86)))
     (logior (loghead 30 lin-addr)
	     (ash (loghead 22 (logtail 30 (combine-bytes bytes)))
		  30)))))
  :hints (("Goal"
	   :do-not-induct t
	   :in-theory (e/d* (ia32e-la-to-pa-page-dir-ptr-table-values-1G-pages-and-write-to-page-dir-ptr-table-entry-addr
			     ia32e-la-to-pa-pml4-table
			     pdpt-base-addr)
			    (page-dir-ptr-table-entry-addr-to-c-program-optimized-form
			     bitops::logand-with-negated-bitmask
			     (:meta acl2::mv-nth-cons-meta)
			     force (force))))))

(defthmd ia32e-la-to-pa-values-1G-pages-and-write-to-page-dir-ptr-table-entry-addr
  ;; Given a 1G page, ia32e-la-to-pa returns the physical address
  ;; corresponding to lin-addr after the PDPTE corresponding to this
  ;; lin-addr has been modified --- the new PDPTE is (combine-bytes
  ;; bytes). The write is expressed in terms of
  ;; write-to-physical-memory, i.e., at the level of physical memory.
  (implies
   (and
    (equal page-dir-ptr-table-entry-addr
	   (page-dir-ptr-table-entry-addr lin-addr (pdpt-base-addr lin-addr (double-rewrite x86))))
    (equal p-addrs (addr-range 8 page-dir-ptr-table-entry-addr))
    (equal page-dir-ptr-table-entry
	   (combine-bytes
	    (mv-nth 1 (rb (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
			  :r (double-rewrite x86)))))
    (equal cpl (cpl x86))

    ;; PML4TE is direct-mapped.
    (direct-map-p
     8 (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)) :r cpl (double-rewrite x86))
    (not
     (mv-nth
      0
      (las-to-pas
       (create-canonical-address-list 8 (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)))
       :r cpl (double-rewrite x86))))
    (disjoint-p$
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)))
       :r cpl (double-rewrite x86)))
     (all-translation-governing-addresses
      (create-canonical-address-list 8 (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)))
      (double-rewrite x86)))

    ;; PDPTE is direct-mapped.
    (direct-map-p
     8 page-dir-ptr-table-entry-addr :r cpl (double-rewrite x86))
    (not
     (mv-nth
      0
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r cpl (double-rewrite x86))))
    (disjoint-p$
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r cpl (double-rewrite x86)))
     (all-translation-governing-addresses
      (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
      (double-rewrite x86)))

    ;; Physical addresses of PML4TE and PDPTE are disjoint.
    ;; (disjoint-p (addr-range 8 (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86))))
    ;;             (addr-range 8 page-dir-ptr-table-entry-addr))
    (disjoint-p$
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r cpl (double-rewrite x86)))
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)))
       :r cpl (double-rewrite x86))))

    (not (mv-nth 0 (ia32e-la-to-pa lin-addr :r cpl (double-rewrite x86))))

    (equal (page-present page-dir-ptr-table-entry)
	   (page-present (combine-bytes bytes)))
    (equal (page-read-write page-dir-ptr-table-entry)
	   (page-read-write (combine-bytes bytes)))
    (equal (page-user-supervisor page-dir-ptr-table-entry)
	   (page-user-supervisor (combine-bytes bytes)))
    (equal (page-execute-disable page-dir-ptr-table-entry)
	   (page-execute-disable (combine-bytes bytes)))
    (equal (page-size page-dir-ptr-table-entry)
	   (page-size (combine-bytes bytes)))
    (equal (page-size page-dir-ptr-table-entry) 1)
    (equal (part-select page-dir-ptr-table-entry :low 13 :high 29)
	   (part-select (combine-bytes bytes) :low 13 :high 29))

    (equal (len bytes) (len p-addrs))
    (byte-listp bytes)
    (canonical-address-p (+ 7 (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86)))))
    (canonical-address-p (+ 7 page-dir-ptr-table-entry-addr))
    (canonical-address-p lin-addr)
    (x86p x86))
   (and
    (equal (mv-nth 0 (ia32e-la-to-pa lin-addr :r cpl (write-to-physical-memory p-addrs bytes x86)))
	   nil)
    (equal (mv-nth 1 (ia32e-la-to-pa lin-addr :r cpl (write-to-physical-memory p-addrs bytes x86)))
	   (logior (loghead 30 lin-addr) (ash (loghead 22 (logtail 30 (combine-bytes bytes))) 30)))))
  :hints (("Goal"
	   :do-not-induct t
	   :in-theory (e/d* (ia32e-la-to-pa-pml4-table-values-1G-pages-and-write-to-page-dir-ptr-table-entry-addr
			     ia32e-la-to-pa
			     pml4-table-base-addr
			     direct-map-p
			     disjoint-p$)
			    (page-dir-ptr-table-entry-addr-to-c-program-optimized-form
			     bitops::logand-with-negated-bitmask
			     (:meta acl2::mv-nth-cons-meta)
			     not
			     force (force))))))

(defthmd ia32e-la-to-pa-values-1G-pages-and-wb-to-page-dir-ptr-table-entry-addr
  ;; Given a 1G page, ia32e-la-to-pa returns the physical address
  ;; corresponding to lin-addr after the PDPTE corresponding to this
  ;; lin-addr has been modified --- the new PDPTE is (combine-bytes
  ;; bytes). The write is expressed in terms of wb, i.e., at the level
  ;; of linear memory.
  (implies
   (and
    ;; Restricting this rule so that it doesn't apply when lin-addr
    ;; points to a paging entry.
    (syntaxp (not (and (consp lin-addr)
		       (or (eq (car lin-addr) 'CAR)
			   (eq (car lin-addr) 'PML4-TABLE-ENTRY-ADDR$INLINE)
			   (eq (car lin-addr) 'PAGE-DIR-PTR-TABLE-ENTRY-ADDR$INLINE)))))
    (equal page-dir-ptr-table-entry-addr
	   (page-dir-ptr-table-entry-addr lin-addr (pdpt-base-addr lin-addr (double-rewrite x86))))
    (equal page-dir-ptr-table-entry
	   (combine-bytes
	    (mv-nth 1 (rb (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
			  :r (double-rewrite x86)))))
    (equal cpl (cpl x86))

    ;; PML4TE is direct-mapped.
    (direct-map-p
     8 (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86)))
     :r cpl (double-rewrite x86))
    (not
     (mv-nth
      0
      (las-to-pas
       (create-canonical-address-list
	8
	(pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86))))
       :r cpl (double-rewrite x86))))
    (disjoint-p$
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list
	8
	(pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86))))
       :r cpl (double-rewrite x86)))
     (all-translation-governing-addresses
      (create-canonical-address-list
       8
       (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86))))
      (double-rewrite x86)))

    ;; PDPTE is direct-mapped.
    (direct-map-p
     8 page-dir-ptr-table-entry-addr :r cpl (double-rewrite x86))
    (not
     (mv-nth
      0
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r cpl (double-rewrite x86))))
    (disjoint-p$
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r cpl (double-rewrite x86)))
     (all-translation-governing-addresses
      (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
      (double-rewrite x86)))

    ;; Physical addresses of PML4TE and PDPTE are disjoint.
    (disjoint-p$
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r cpl (double-rewrite x86)))
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)))
       :r cpl (double-rewrite x86))))
    ;; (disjoint-p (addr-range 8 (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86))))
    ;;             (addr-range 8 page-dir-ptr-table-entry-addr))

    (equal (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) (double-rewrite x86)))
	   (addr-range 8 page-dir-ptr-table-entry-addr))

    (disjoint-p
     (mv-nth 1
	     (las-to-pas
	      (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
	      :r cpl (double-rewrite x86)))
     (all-translation-governing-addresses (strip-cars addr-lst) (double-rewrite x86)))

    (not (mv-nth 0 (ia32e-la-to-pa lin-addr :r cpl (double-rewrite x86))))

    (equal (page-present page-dir-ptr-table-entry)
	   (page-present (combine-bytes (strip-cdrs addr-lst))))
    (equal (page-read-write page-dir-ptr-table-entry)
	   (page-read-write (combine-bytes (strip-cdrs addr-lst))))
    (equal (page-user-supervisor page-dir-ptr-table-entry)
	   (page-user-supervisor (combine-bytes (strip-cdrs addr-lst))))
    (equal (page-execute-disable page-dir-ptr-table-entry)
	   (page-execute-disable (combine-bytes (strip-cdrs addr-lst))))
    (equal (page-size page-dir-ptr-table-entry)
	   (page-size (combine-bytes (strip-cdrs addr-lst))))
    (equal (page-size page-dir-ptr-table-entry) 1)
    (equal (part-select page-dir-ptr-table-entry :low 13 :high 29)
	   (part-select (combine-bytes (strip-cdrs addr-lst)) :low 13 :high 29))

    (addr-byte-alistp addr-lst)
    (canonical-address-p (+ 7 (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86)))))
    (canonical-address-p (+ 7 page-dir-ptr-table-entry-addr))
    (canonical-address-p lin-addr)
    (x86p x86))
   (and
    (equal (mv-nth 0 (ia32e-la-to-pa lin-addr :r cpl (mv-nth 1 (wb addr-lst x86))))
	   nil)
    (equal (mv-nth 1 (ia32e-la-to-pa lin-addr :r cpl (mv-nth 1 (wb addr-lst x86))))
	   (logior
	    (loghead 30 lin-addr)
	    (ash (loghead 22 (logtail 30 (combine-bytes (strip-cdrs addr-lst)))) 30)))))
  :hints
  (("Goal"
    :do-not-induct t
    :in-theory (e/d*
		(ia32e-la-to-pa-values-1G-pages-and-write-to-page-dir-ptr-table-entry-addr
		 wb
		 pdpt-base-addr
		 page-dir-ptr-table-entry-addr
		 pml4-table-base-addr)
		(member-p-canonical-address-listp
		 subset-p
		 mv-nth-0-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p
		 cdr-mv-nth-1-las-to-pas
		 unsigned-byte-p-of-combine-bytes
		 acl2::loghead-identity
		 mv-nth-0-las-to-pas-subset-p
		 rewrite-rb-to-rb-alt
		 member-p-strip-cars-of-remove-duplicate-keys
		 page-dir-ptr-table-entry-addr-to-c-program-optimized-form
		 bitops::logand-with-negated-bitmask
		 (:meta acl2::mv-nth-cons-meta)
		 not force (force))))))

;; Now generalizing
;; ia32e-la-to-pa-values-1G-pages-and-wb-to-page-dir-ptr-table-entry-addr
;; to las-to-pas:

(defthmd mv-nth-0-las-to-pas-cons
  (equal (mv-nth 0 (las-to-pas (cons e x) r-w-x cpl x86))
	 (if (mv-nth 0 (ia32e-la-to-pa e r-w-x cpl x86))
	     (mv-nth 0 (ia32e-la-to-pa e r-w-x cpl x86))
	   (mv-nth 0 (las-to-pas x r-w-x cpl x86))))
  :hints (("Goal" :in-theory (e/d* (las-to-pas) ()))))

(defthmd mv-nth-1-las-to-pas-cons
  (implies (not (mv-nth 0 (las-to-pas (cons e x) r-w-x cpl x86)))
	   (equal (mv-nth 1 (las-to-pas (cons e x) r-w-x cpl x86))
		  (cons (mv-nth 1 (ia32e-la-to-pa e r-w-x cpl x86))
			(mv-nth 1 (las-to-pas x r-w-x cpl x86)))))
  :hints (("Goal" :in-theory (e/d* (las-to-pas) ()))))

(defthmd las-to-pas-values-1G-pages-and-wb-to-page-dir-ptr-table-entry-addr-general
  ;; las-to-pas returns the physical addresses corresponding to linear
  ;; addresses after the PDPTE corresponding to these linear addresses
  ;; have been modified --- the new PDPTE is (combine-bytes
  ;; (strip-cdrs addr-lst)).
  (implies
   (and
    (equal page-dir-ptr-table-entry-addr
	   (page-dir-ptr-table-entry-addr lin-addr (pdpt-base-addr lin-addr (double-rewrite x86))))
    (equal page-dir-ptr-table-entry
	   (combine-bytes
	    (mv-nth 1 (rb (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
			  :r (double-rewrite x86)))))
    (equal cpl (cpl x86))

    ;; PML4TE is direct-mapped.
    (direct-map-p
     8 (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86)))
     :r cpl (double-rewrite x86))
    (not
     (mv-nth
      0
      (las-to-pas
       (create-canonical-address-list
	8
	(pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86))))
       :r cpl (double-rewrite x86))))
    (disjoint-p$
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list
	8
	(pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86))))
       :r cpl (double-rewrite x86)))
     (all-translation-governing-addresses
      (create-canonical-address-list
       8
       (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86))))
      (double-rewrite x86)))

    ;; PDPTE is direct-mapped.
    (direct-map-p
     8 page-dir-ptr-table-entry-addr :r cpl (double-rewrite x86))
    (not
     (mv-nth
      0
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r cpl (double-rewrite x86))))
    (disjoint-p$
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r cpl (double-rewrite x86)))
     (all-translation-governing-addresses
      (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
      (double-rewrite x86)))

    ;; Physical addresses of PML4TE and PDPTE are disjoint.
    (disjoint-p$
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r cpl (double-rewrite x86)))
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)))
       :r cpl (double-rewrite x86))))
    ;; (disjoint-p (addr-range 8 (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86))))
    ;;             (addr-range 8 page-dir-ptr-table-entry-addr))

    (equal (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) (double-rewrite x86)))
	   (addr-range 8 page-dir-ptr-table-entry-addr))

    (disjoint-p
     (mv-nth 1
	     (las-to-pas
	      (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
	      :r cpl (double-rewrite x86)))
     (all-translation-governing-addresses (strip-cars addr-lst) (double-rewrite x86)))

    (not (mv-nth 0 (ia32e-la-to-pa lin-addr :r cpl (double-rewrite x86))))

    (equal (page-present page-dir-ptr-table-entry)
	   (page-present (combine-bytes (strip-cdrs addr-lst))))
    (equal (page-read-write page-dir-ptr-table-entry)
	   (page-read-write (combine-bytes (strip-cdrs addr-lst))))
    (equal (page-user-supervisor page-dir-ptr-table-entry)
	   (page-user-supervisor (combine-bytes (strip-cdrs addr-lst))))
    (equal (page-execute-disable page-dir-ptr-table-entry)
	   (page-execute-disable (combine-bytes (strip-cdrs addr-lst))))
    (equal (page-size page-dir-ptr-table-entry)
	   (page-size (combine-bytes (strip-cdrs addr-lst))))
    (equal (page-size page-dir-ptr-table-entry) 1)
    (equal (part-select page-dir-ptr-table-entry :low 13 :high 29)
	   (part-select (combine-bytes (strip-cdrs addr-lst)) :low 13 :high 29))

    (addr-byte-alistp addr-lst)
    (canonical-address-p (+ 7 (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86)))))
    (canonical-address-p (+ 7 page-dir-ptr-table-entry-addr))
    (canonical-address-p lin-addr)
    (canonical-address-p (+ -1 lin-addr m))
    (natp m)
    (<= m *2^30*)
    (natp iteration)
    (equal (loghead 30 lin-addr) 0)
    (not (programmer-level-mode x86))
    (x86p x86))
   ;; las-to-pas returns the physical addresses corresponding to
   ;; linear addresses after the PDPTE corresponding to these linear
   ;; addresses have been modified --- the new PDPTE is (combine-bytes
   ;; (strip-cdrs addr-lst)).
   (and
    (equal (mv-nth 0 (las-to-pas
		      (create-canonical-address-list-alt iteration m lin-addr)
		      :r cpl (mv-nth 1 (wb addr-lst x86))))
	   nil)
    (equal (mv-nth 1 (las-to-pas
		      (create-canonical-address-list-alt iteration m lin-addr)
		      :r cpl (mv-nth 1 (wb addr-lst x86))))
	   (addr-range
	    (+ (- iteration) m)
	    (+ iteration
	       (ash (loghead 22 (logtail 30 (combine-bytes (strip-cdrs addr-lst)))) 30))))))
  :hints (("Goal"
	   :induct (create-canonical-address-list-alt iteration m lin-addr)
	   :in-theory (e/d*
		       ( ;; disjoint-p$
			;; direct-map-p
			page-dir-ptr-table-entry-addr
			pdpt-base-addr
			mv-nth-0-las-to-pas-cons
			mv-nth-1-las-to-pas-cons
			open-mv-nth-1-las-to-pas-for-same-1G-page-general-1
			open-mv-nth-0-las-to-pas-for-same-1G-page-general-1
			open-mv-nth-0-las-to-pas-for-same-1G-page-general-2
			ia32e-la-to-pa-values-for-same-1G-page
			ia32e-la-to-pa-values-1G-pages-and-wb-to-page-dir-ptr-table-entry-addr)
		       (acl2::loghead-identity
			acl2::zip-open
			member-p-addr-range
			not-member-p-addr-range
			unsigned-byte-p-of-combine-bytes-and-rb-in-system-level-mode
			direct-map-p-and-wb-disjoint-from-xlation-governing-addrs
			len-of-rb-in-system-level-mode
			(:linear ash-monotone-2)
			unsigned-byte-p-of-combine-bytes
			cdr-mv-nth-1-las-to-pas
			rewrite-rb-to-rb-alt
			mv-nth-0-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p
			member-p-canonical-address-listp
			pml4-table-entry-addr-to-c-program-optimized-form
			adding-7-to-pml4-table-entry-addr
			rb-wb-disjoint-in-system-level-mode
			cdr-create-canonical-address-list
			ia32e-la-to-pa-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs
			car-mv-nth-1-las-to-pas
			mv-nth-1-las-to-pas-subset-p
			subset-p-two-create-canonical-address-lists-general
			member-p-strip-cars-of-remove-duplicate-keys
			page-dir-ptr-table-entry-addr-to-c-program-optimized-form
			bitops::logand-with-negated-bitmask
			force (force)
			not)))))

(defthm las-to-pas-values-1G-pages-and-wb-to-page-dir-ptr-table-entry-addr
  ;; las-to-pas returns the physical addresses corresponding to linear
  ;; addresses after the PDPTE corresponding to these linear addresses
  ;; have been modified --- the new PDPTE is (combine-bytes
  ;; (strip-cdrs addr-lst)).
  (implies
   (and
    (equal page-dir-ptr-table-entry-addr
	   (page-dir-ptr-table-entry-addr lin-addr (pdpt-base-addr lin-addr (double-rewrite x86))))
    (equal page-dir-ptr-table-entry
	   (combine-bytes
	    (mv-nth 1 (rb (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
			  :r (double-rewrite x86)))))
    (equal cpl (cpl x86))

    ;; PML4TE is direct-mapped.
    (direct-map-p
     8 (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86)))
     :r cpl (double-rewrite x86))
    (not
     (mv-nth
      0
      (las-to-pas
       (create-canonical-address-list
	8
	(pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86))))
       :r cpl (double-rewrite x86))))
    (disjoint-p$
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list
	8
	(pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86))))
       :r cpl (double-rewrite x86)))
     (all-translation-governing-addresses
      (create-canonical-address-list
       8
       (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86))))
      (double-rewrite x86)))

    ;; PDPTE is direct-mapped.
    (direct-map-p
     8 page-dir-ptr-table-entry-addr :r cpl (double-rewrite x86))
    (not
     (mv-nth
      0
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r cpl (double-rewrite x86))))
    (disjoint-p$
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r cpl (double-rewrite x86)))
     (all-translation-governing-addresses
      (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
      (double-rewrite x86)))

    ;; Physical addresses of PML4TE and PDPTE are disjoint.
    (disjoint-p$
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r cpl (double-rewrite x86)))
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)))
       :r cpl (double-rewrite x86))))
    ;; (disjoint-p (addr-range 8 (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86))))
    ;;             (addr-range 8 page-dir-ptr-table-entry-addr))

    (equal (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) (double-rewrite x86)))
	   ;; (addr-range 8 page-dir-ptr-table-entry-addr)
	   (mv-nth
	    1
	    (las-to-pas
	     (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
	     :r cpl (double-rewrite x86))))

    (disjoint-p
     (mv-nth 1
	     (las-to-pas
	      (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
	      :r cpl (double-rewrite x86)))
     (all-translation-governing-addresses (strip-cars addr-lst) (double-rewrite x86)))

    (not (mv-nth 0 (las-to-pas
		    (create-canonical-address-list *2^30* lin-addr)
		    :r cpl (double-rewrite x86))))

    (equal (page-present page-dir-ptr-table-entry)
	   (page-present (combine-bytes (strip-cdrs addr-lst))))
    (equal (page-read-write page-dir-ptr-table-entry)
	   (page-read-write (combine-bytes (strip-cdrs addr-lst))))
    (equal (page-user-supervisor page-dir-ptr-table-entry)
	   (page-user-supervisor (combine-bytes (strip-cdrs addr-lst))))
    (equal (page-execute-disable page-dir-ptr-table-entry)
	   (page-execute-disable (combine-bytes (strip-cdrs addr-lst))))
    (equal (page-size page-dir-ptr-table-entry)
	   (page-size (combine-bytes (strip-cdrs addr-lst))))
    (equal (page-size page-dir-ptr-table-entry) 1)
    (equal (part-select page-dir-ptr-table-entry :low 13 :high 29)
	   (part-select (combine-bytes (strip-cdrs addr-lst)) :low 13 :high 29))

    (addr-byte-alistp addr-lst)
    (canonical-address-p (+ 7 (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86)))))
    (canonical-address-p (+ 7 page-dir-ptr-table-entry-addr))
    (canonical-address-p lin-addr)
    (equal (loghead 30 lin-addr) 0)
    (not (programmer-level-mode x86))
    (x86p x86))
   (and
    (equal (mv-nth 0 (las-to-pas
		      (create-canonical-address-list *2^30* lin-addr)
		      :r cpl (mv-nth 1 (wb addr-lst x86))))
	   nil)
    (equal (mv-nth 1 (las-to-pas
		      (create-canonical-address-list *2^30* lin-addr)
		      :r cpl (mv-nth 1 (wb addr-lst x86))))
	   (addr-range *2^30* (ash (loghead 22 (logtail 30 (combine-bytes (strip-cdrs addr-lst)))) 30)))))
  :hints (("Goal"
	   :do-not '(preprocess)
	   :do-not-induct t
	   :use ((:instance las-to-pas-values-1G-pages-and-wb-to-page-dir-ptr-table-entry-addr-general
			    (m *2^30*)
			    (iteration 0))
		 (:instance open-mv-nth-1-las-to-pas-for-same-1G-page-general-2))
	   :in-theory (e/d* (create-canonical-address-list-alt-is-create-canonical-address-list
			     direct-map-p)
			    (member-p-strip-cars-of-remove-duplicate-keys
			     page-dir-ptr-table-entry-addr-to-c-program-optimized-form
			     bitops::logand-with-negated-bitmask
			     force (force)
			     not)))))

;; ======================================================================

;; Begin proof of
;; all-translation-governing-addresses-1G-pages-and-wb-to-page-dir-ptr-table-entry-addr:

;; First, we compute the translation-governing addresses corresponding
;; to (+ n lin-addr), given that (+ n lin-addr) lies in the same 1G
;; page as lin-addr.  We then generalize this result to
;; all-translation-governing-addresses (from
;; translation-governing-addresses).

(defthmd translation-governing-addresses-for-same-1G-page
  ;; Similar to ia32e-la-to-pa-values-for-same-1G-page, but for
  ;; translation-governing-addresses.
  (implies
   (and
    (equal cpl (cpl x86))
    (equal pml4-table-base-addr (pml4-table-base-addr x86))
    (equal pml4-table-entry-addr (pml4-table-entry-addr lin-addr pml4-table-base-addr))
    (equal pdpt-base-addr (pdpt-base-addr lin-addr x86))
    (equal page-dir-ptr-table-entry-addr
	   (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
    (equal page-dir-ptr-table-entry
	   (combine-bytes
	    (mv-nth
	     1
	     (rb (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
		 :r x86))))
    (direct-map-p 8 pml4-table-entry-addr :r cpl (double-rewrite x86))
    (not
     (mv-nth
      0
      (las-to-pas (create-canonical-address-list 8 pml4-table-entry-addr)
		  :r cpl x86)))
    (disjoint-p$
     (mv-nth
      1
      (las-to-pas (create-canonical-address-list 8 pml4-table-entry-addr)
		  :r cpl x86))
     (all-translation-governing-addresses
      (create-canonical-address-list 8 pml4-table-entry-addr)
      x86))
    (direct-map-p 8 page-dir-ptr-table-entry-addr :r cpl (double-rewrite x86))
    (not
     (mv-nth
      0
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r cpl x86)))
    (disjoint-p$
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r cpl x86))
     (all-translation-governing-addresses
      (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
      x86))
    (equal (page-size page-dir-ptr-table-entry) 1)
    (canonical-address-p (+ 7 pml4-table-entry-addr))
    (canonical-address-p (+ 7 page-dir-ptr-table-entry-addr))
    (canonical-address-p lin-addr)
    (canonical-address-p (+ n lin-addr))
    (equal (loghead 30 (+ n lin-addr)) n)
    (unsigned-byte-p 30 n)
    (x86p x86))
   (equal (translation-governing-addresses (+ n lin-addr) x86)
	  (translation-governing-addresses lin-addr x86)))
  :hints (("Goal"
	   :in-theory (e/d* (translation-governing-addresses
			     translation-governing-addresses-for-pml4-table
			     translation-governing-addresses-for-page-dir-ptr-table
			     disjoint-p$
			     direct-map-p
			     pdpt-base-addr
			     pml4-table-base-addr)
			    (commutativity-of-+
			     subset-p
			     (:linear acl2::loghead-upper-bound)
			     unsigned-byte-p-of-logtail
			     member-p
			     member-p-canonical-address-listp
			     unsigned-byte-p-of-logtail
			     mv-nth-0-las-to-pas-subset-p
			     not
			     pml4-table-entry-addr-to-c-program-optimized-form
			     bitops::logand-with-negated-bitmask)))))

(local
 (defun repeat (n x)
   ;; This is similar to acl2::repeat, except that it is in terms of
   ;; append instead of cons.
   (declare (xargs :guard (and (natp n) (true-listp x))))
   (if (zp n) nil (append x (repeat (- n 1) x)))))

(local
 (defthmd all-translation-governing-addresses-1G-pages-general
   (implies
    (and
     (equal cpl (cpl x86))
     (equal pml4-table-base-addr (pml4-table-base-addr x86))
     (equal pml4-table-entry-addr (pml4-table-entry-addr lin-addr pml4-table-base-addr))
     (equal pdpt-base-addr (pdpt-base-addr lin-addr x86))
     (equal page-dir-ptr-table-entry-addr (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
     (equal page-dir-ptr-table-entry
	    (combine-bytes
	     (mv-nth
	      1
	      (rb (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
		  :r x86))))
     (direct-map-p 8 pml4-table-entry-addr :r cpl (double-rewrite x86))
     (not
      (mv-nth
       0
       (las-to-pas (create-canonical-address-list 8 pml4-table-entry-addr)
		   :r cpl x86)))
     (disjoint-p$
      (mv-nth
       1
       (las-to-pas (create-canonical-address-list 8 pml4-table-entry-addr)
		   :r cpl x86))
      (all-translation-governing-addresses
       (create-canonical-address-list 8 pml4-table-entry-addr)
       x86))
     (direct-map-p 8 page-dir-ptr-table-entry-addr :r cpl (double-rewrite x86))
     (not
      (mv-nth
       0
       (las-to-pas
	(create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
	:r cpl x86)))
     (disjoint-p$
      (mv-nth
       1
       (las-to-pas
	(create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
	:r cpl x86))
      (all-translation-governing-addresses
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       x86))
     (equal (page-size page-dir-ptr-table-entry) 1)
     (canonical-address-p (+ 7 pml4-table-entry-addr))
     (canonical-address-p (+ 7 page-dir-ptr-table-entry-addr))
     (canonical-address-p lin-addr)
     (canonical-address-p (+ -1 lin-addr m))
     (natp m)
     (<= m *2^30*)
     (natp iteration)
     (equal (loghead 30 lin-addr) 0)
     (x86p x86))
    (equal
     (all-translation-governing-addresses (create-canonical-address-list-alt iteration m lin-addr) x86)
     (repeat (- m iteration) (translation-governing-addresses lin-addr x86))))
   :hints (("Goal"
	    :induct (create-canonical-address-list-alt iteration m lin-addr)
	    :do-not '(preprocess)
	    :in-theory (e/d* (all-translation-governing-addresses
			      translation-governing-addresses-for-same-1G-page)
			     (member-p-strip-cars-of-remove-duplicate-keys
			      page-dir-ptr-table-entry-addr-to-c-program-optimized-form
			      bitops::logand-with-negated-bitmask
			      force (force)
			      not))))))

(local
 (defthmd all-translation-governing-addresses-1G-pages
   (implies
    (and
     (equal cpl (cpl x86))
     (equal pml4-table-base-addr (pml4-table-base-addr x86))
     (equal pml4-table-entry-addr (pml4-table-entry-addr lin-addr pml4-table-base-addr))
     (equal pml4-table-entry
	    (combine-bytes
	     (mv-nth 1
		     (rb (create-canonical-address-list 8 pml4-table-entry-addr)
			 :r x86))))
     (equal pdpt-base-addr (pdpt-base-addr lin-addr x86))
     (equal page-dir-ptr-table-entry-addr
	    (page-dir-ptr-table-entry-addr lin-addr pdpt-base-addr))
     (equal
      page-dir-ptr-table-entry
      (combine-bytes
       (mv-nth
	1
	(rb (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
	    :r x86))))
     (direct-map-p 8 pml4-table-entry-addr :r cpl (double-rewrite x86))
     (not
      (mv-nth
       0
       (las-to-pas (create-canonical-address-list 8 pml4-table-entry-addr)
		   :r cpl x86)))
     (disjoint-p$
      (mv-nth
       1
       (las-to-pas (create-canonical-address-list 8 pml4-table-entry-addr)
		   :r cpl x86))
      (all-translation-governing-addresses
       (create-canonical-address-list 8 pml4-table-entry-addr)
       x86))
     (direct-map-p 8 page-dir-ptr-table-entry-addr :r cpl (double-rewrite x86))
     (not
      (mv-nth
       0
       (las-to-pas
	(create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
	:r cpl x86)))
     (disjoint-p$
      (mv-nth
       1
       (las-to-pas
	(create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
	:r cpl x86))
      (all-translation-governing-addresses
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       x86))
     (disjoint-p$
      (mv-nth
       1
       (las-to-pas
	(create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
	:r cpl (double-rewrite x86)))
      (mv-nth
       1
       (las-to-pas
	(create-canonical-address-list 8 pml4-table-entry-addr)
	:r cpl (double-rewrite x86))))
     (equal (page-size page-dir-ptr-table-entry) 1)

     (not (mv-nth 0 (las-to-pas
		     (create-canonical-address-list *2^30* lin-addr)
		     :r cpl (double-rewrite x86))))

     (canonical-address-p (+ 7 pml4-table-entry-addr))
     (canonical-address-p (+ 7 page-dir-ptr-table-entry-addr))

     (canonical-address-p lin-addr)
     (equal (loghead 30 lin-addr) 0)
     (canonical-address-p (+ -1 lin-addr m))
     (natp m)
     (<= m *2^30*)
     (x86p x86))
    (equal
     (all-translation-governing-addresses (create-canonical-address-list m lin-addr) x86)
     (repeat m (translation-governing-addresses lin-addr x86))))
   :hints (("Goal"
	    :do-not '(preprocess)
	    :use ((:instance all-translation-governing-addresses-1G-pages-general
			     (iteration 0)))
	    :in-theory (e/d* (create-canonical-address-list-alt-is-create-canonical-address-list)
			     (member-p-strip-cars-of-remove-duplicate-keys
			      page-dir-ptr-table-entry-addr-to-c-program-optimized-form
			      bitops::logand-with-negated-bitmask
			      force (force)
			      not))))))


;; Reading the new translation-governing addresses of a lin-addr,
;; given that its PDPTE has been modified:

(local
 (defthmd rm-low-64-and-write-to-physical-memory-disjoint-commuted
   (implies (disjoint-p p-addrs-2 (addr-range 8 p-addr-1))
	    (equal (rm-low-64 p-addr-1 (write-to-physical-memory p-addrs-2 bytes x86))
		   (rm-low-64 p-addr-1 x86)))
   :hints (("Goal" :in-theory (e/d* (disjoint-p-commutative) ())))))

(defthmd translation-governing-addresses-1G-pages-and-wb-to-page-dir-ptr-table-entry-addr
  ;; Similar to
  ;; ia32e-la-to-pa-values-1G-pages-and-wb-to-page-dir-ptr-table-entry-addr
  ;; for
  ;; translation-governing-addresses.
  (implies
   ;; Restricting this rule so that it doesn't apply when lin-addr
   ;; points to a paging entry.
   (and
    (syntaxp (not (and (consp lin-addr)
		       (or (eq (car lin-addr) 'car)
			   (eq (car lin-addr) 'pml4-table-entry-addr$inline)
			   (eq (car lin-addr) 'page-dir-ptr-table-entry-addr$inline)))))
    (equal page-dir-ptr-table-entry-addr
	   (page-dir-ptr-table-entry-addr lin-addr (pdpt-base-addr lin-addr (double-rewrite x86))))
    (equal page-dir-ptr-table-entry
	   (combine-bytes
	    (mv-nth
	     1
	     (rb (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
		 :r (double-rewrite x86)))))
    (equal cpl (cpl x86))
    (direct-map-p
     8
     (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86)))
     :r cpl (double-rewrite x86))
    (not
     (mv-nth
      0
      (las-to-pas
       (create-canonical-address-list
	8
	(pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86))))
       :r cpl (double-rewrite x86))))
    (disjoint-p$
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list
	8
	(pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86))))
       :r cpl (double-rewrite x86)))
     (all-translation-governing-addresses
      (create-canonical-address-list
       8
       (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86))))
      (double-rewrite x86)))
    (direct-map-p 8 page-dir-ptr-table-entry-addr :r cpl (double-rewrite x86))
    (not
     (mv-nth
      0
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r cpl (double-rewrite x86))))
    (disjoint-p$
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r cpl (double-rewrite x86)))
     (all-translation-governing-addresses
      (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
      (double-rewrite x86)))
    (disjoint-p$
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r cpl (double-rewrite x86)))
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list
	8 (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)))
       :r cpl (double-rewrite x86))))
    (equal (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) (double-rewrite x86)))
	   (addr-range 8 page-dir-ptr-table-entry-addr))
    (disjoint-p
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r cpl (double-rewrite x86)))
     (all-translation-governing-addresses (strip-cars addr-lst)
					  (double-rewrite x86)))
    (equal (page-size page-dir-ptr-table-entry)
	   (page-size (combine-bytes (strip-cdrs addr-lst))))
    (equal (page-size page-dir-ptr-table-entry) 1)
    (addr-byte-alistp addr-lst)
    (canonical-address-p
     (+ 7 (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86)))))
    (canonical-address-p (+ 7 page-dir-ptr-table-entry-addr))
    (x86p x86))
   (equal (translation-governing-addresses lin-addr (mv-nth 1 (wb addr-lst x86)))
	  (translation-governing-addresses lin-addr x86)))
  :hints
  (("Goal"
    :do-not-induct t
    :use ((:instance xlate-equiv-entries-and-page-size
		     (e-1 (rm-low-64
			   (pml4-table-entry-addr
			    lin-addr
			    (pml4-table-base-addr x86))
			   (mv-nth
			    2
			    (las-to-pas
			     (strip-cars addr-lst) :w (cpl x86)
			     (write-to-physical-memory
			      (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86))
			      (strip-cdrs addr-lst) x86)))))
		     (e-2 (rm-low-64 (pml4-table-entry-addr
				      lin-addr
				      (pml4-table-base-addr x86))
				     x86))))
    :in-theory (e/d*
		(disjoint-p$
		 wb
		 direct-map-p
		 pml4-table-base-addr
		 pdpt-base-addr
		 translation-governing-addresses
		 translation-governing-addresses-for-pml4-table
		 translation-governing-addresses-for-page-dir-ptr-table
		 rm-low-64-and-write-to-physical-memory-disjoint-commuted)

		(rm-low-64-and-write-to-physical-memory-disjoint
		 rewrite-rb-to-rb-alt
		 subset-p
		 member-p
		 cdr-mv-nth-1-las-to-pas
		 mv-nth-0-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p
		 member-p-canonical-address-listp
		 mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs-alt
		 mv-nth-0-las-to-pas-subset-p
		 (:linear adding-7-to-pml4-table-entry-addr)
		 member-p-strip-cars-of-remove-duplicate-keys
		 pml4-table-entry-addr-to-c-program-optimized-form
		 page-dir-ptr-table-entry-addr-to-c-program-optimized-form
		 bitops::logand-with-negated-bitmask
		 (:meta acl2::mv-nth-cons-meta)
		 not force (force))))))


(local
 (defthmd translation-governing-addresses-for-same-1G-page-and-wb-to-page-dir-ptr-table-entry-addr-helper
   (implies
    (and
     (equal page-dir-ptr-table-entry-addr
	    (page-dir-ptr-table-entry-addr
	     lin-addr
	     (pdpt-base-addr lin-addr (double-rewrite x86))))
     (equal page-dir-ptr-table-entry
	    (combine-bytes
	     (mv-nth
	      1
	      (rb (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
		  :r (double-rewrite x86)))))
     (equal cpl (cpl x86))
     (direct-map-p
      8
      (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86)))
      :r cpl (double-rewrite x86))
     (not
      (mv-nth
       0
       (las-to-pas
	(create-canonical-address-list
	 8
	 (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86))))
	:r cpl (double-rewrite x86))))
     (disjoint-p$
      (mv-nth
       1
       (las-to-pas
	(create-canonical-address-list
	 8
	 (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86))))
	:r cpl (double-rewrite x86)))
      (all-translation-governing-addresses
       (create-canonical-address-list
	8 (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86))))
       (double-rewrite x86)))

     (direct-map-p 8 page-dir-ptr-table-entry-addr :r cpl (double-rewrite x86))

     (not
      (mv-nth
       0
       (las-to-pas
	(create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
	:r cpl (double-rewrite x86))))
     (disjoint-p$
      (mv-nth
       1
       (las-to-pas
	(create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
	:r cpl (double-rewrite x86)))
      (all-translation-governing-addresses
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       (double-rewrite x86)))
     (disjoint-p$
      (mv-nth
       1
       (las-to-pas
	(create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
	:r cpl (double-rewrite x86)))
      (mv-nth
       1
       (las-to-pas
	(create-canonical-address-list
	 8
	 (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)))
	:r cpl (double-rewrite x86))))
     (equal (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) (double-rewrite x86)))
	    (addr-range 8 page-dir-ptr-table-entry-addr))
     (disjoint-p
      (mv-nth
       1
       (las-to-pas
	(create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
	:r cpl (double-rewrite x86)))
      (all-translation-governing-addresses (strip-cars addr-lst) (double-rewrite x86)))
     (equal (page-size page-dir-ptr-table-entry)
	    (page-size (combine-bytes (strip-cdrs addr-lst))))
     (addr-byte-alistp addr-lst)
     (canonical-address-p
      (+ 7 (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86)))))
     (canonical-address-p (+ 7 page-dir-ptr-table-entry-addr))
     (canonical-address-p lin-addr)
     (canonical-address-p (+ n lin-addr))
     (equal (loghead 30 (+ n lin-addr)) n)
     (unsigned-byte-p 30 n)
     (not (programmer-level-mode x86))
     (x86p x86))
    (and
     (equal
      (page-size
       (rm-low-64 (pml4-table-entry-addr
		   lin-addr
		   (ash (loghead 40 (logtail 12 (xr :ctr *cr3* x86))) 12))
		  (mv-nth 1 (wb addr-lst x86))))
      (page-size
       (rm-low-64 (pml4-table-entry-addr
		   lin-addr
		   (ash (loghead 40 (logtail 12 (xr :ctr *cr3* x86))) 12))
		  x86)))

     (equal
      (page-size
       (rm-low-64
	(page-dir-ptr-table-entry-addr
	 lin-addr
	 (ash
	  (loghead
	   40
	   (logtail
	    12
	    (rm-low-64 (pml4-table-entry-addr
			lin-addr
			(ash (loghead 40 (logtail 12 (xr :ctr *cr3* x86)))
			     12))
		       x86)))
	  12))
	x86))
      (page-size
       (rm-low-64
	(page-dir-ptr-table-entry-addr
	 lin-addr
	 (ash
	  (loghead
	   40
	   (logtail
	    12
	    (rm-low-64 (pml4-table-entry-addr
			lin-addr
			(ash (loghead 40 (logtail 12 (xr :ctr *cr3* x86))) 12))
		       x86)))
	  12))
	(mv-nth 1 (wb addr-lst x86)))))

     (equal
      (logtail
       12
       (rm-low-64 (pml4-table-entry-addr
		   lin-addr
		   (ash (loghead 40 (logtail 12 (xr :ctr *cr3* x86))) 12))
		  (mv-nth 1 (wb addr-lst x86))))
      (logtail
       12
       (rm-low-64 (pml4-table-entry-addr
		   lin-addr
		   (ash (loghead 40 (logtail 12 (xr :ctr *cr3* x86))) 12))
		  x86)))))
   :hints (("Goal"
	    :do-not-induct t
	    :use ((:instance xlate-equiv-entries-and-page-size
			     (e-1 (rm-low-64
				   (pml4-table-entry-addr
				    lin-addr (pml4-table-base-addr x86))
				   (mv-nth
				    2
				    (las-to-pas
				     (strip-cars addr-lst) :w (cpl x86)
				     (write-to-physical-memory
				      (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) x86))
				      (strip-cdrs addr-lst)
				      x86)))))
			     (e-2 (rm-low-64
				   (pml4-table-entry-addr
				    lin-addr (pml4-table-base-addr x86))
				   x86))))
	    :in-theory (e/d* (disjoint-p$
			      wb
			      direct-map-p
			      rm-low-64-and-write-to-physical-memory-disjoint-commuted
			      pml4-table-base-addr
			      pdpt-base-addr)
			     (rm-low-64-and-write-to-physical-memory-disjoint
			      commutativity-of-+
			      remove-duplicate-keys
			      member-p-strip-cars-of-remove-duplicate-keys
			      pml4-table-entry-addr-to-c-program-optimized-form
			      page-dir-ptr-table-entry-addr-to-c-program-optimized-form
			      bitops::logand-with-negated-bitmask
			      force (force)
			      not
			      bitops::logand-with-negated-bitmask))))))

(defthmd translation-governing-addresses-for-same-1G-page-and-wb-to-page-dir-ptr-table-entry-addr
  (implies
   (and
    (syntaxp (not (and (consp lin-addr)
		       (or (eq (car lin-addr) 'car)
			   (eq (car lin-addr) 'pml4-table-entry-addr$inline)
			   (eq (car lin-addr) 'page-dir-ptr-table-entry-addr$inline)))))
    (equal page-dir-ptr-table-entry-addr
	   (page-dir-ptr-table-entry-addr lin-addr (pdpt-base-addr lin-addr (double-rewrite x86))))
    (equal page-dir-ptr-table-entry
	   (combine-bytes
	    (mv-nth
	     1
	     (rb (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
		 :r (double-rewrite x86)))))
    (equal cpl (cpl x86))
    (direct-map-p
     8
     (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86)))
     :r cpl (double-rewrite x86))
    (not
     (mv-nth
      0
      (las-to-pas
       (create-canonical-address-list
	8
	(pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86))))
       :r cpl (double-rewrite x86))))
    (disjoint-p$
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list
	8
	(pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86))))
       :r cpl (double-rewrite x86)))
     (all-translation-governing-addresses
      (create-canonical-address-list
       8
       (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86))))
      (double-rewrite x86)))
    (direct-map-p 8 page-dir-ptr-table-entry-addr :r cpl (double-rewrite x86))
    (not
     (mv-nth
      0
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r cpl (double-rewrite x86))))
    (disjoint-p$
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r cpl (double-rewrite x86)))
     (all-translation-governing-addresses
      (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
      (double-rewrite x86)))
    (disjoint-p$
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r cpl (double-rewrite x86)))
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list
	8 (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)))
       :r cpl (double-rewrite x86))))
    (equal (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) (double-rewrite x86)))
	   (addr-range 8 page-dir-ptr-table-entry-addr))
    (disjoint-p
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r cpl (double-rewrite x86)))
     (all-translation-governing-addresses (strip-cars addr-lst)
					  (double-rewrite x86)))
    (equal (page-size page-dir-ptr-table-entry)
	   (page-size (combine-bytes (strip-cdrs addr-lst))))
    (equal (page-size page-dir-ptr-table-entry) 1)
    (addr-byte-alistp addr-lst)
    (canonical-address-p
     (+ 7 (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86)))))
    (canonical-address-p (+ 7 page-dir-ptr-table-entry-addr))

    (canonical-address-p lin-addr)
    (canonical-address-p (+ n lin-addr))
    (equal (loghead 30 (+ n lin-addr)) n)
    (unsigned-byte-p 30 n)
    (not (programmer-level-mode x86))
    (x86p x86))
   (equal (translation-governing-addresses (+ n lin-addr) (mv-nth 1 (wb addr-lst x86)))
	  (translation-governing-addresses lin-addr x86)))
  :hints (("Goal"
	   :do-not-induct t
	   :use ((:instance translation-governing-addresses-for-same-1G-page-and-wb-to-page-dir-ptr-table-entry-addr-helper))
	   :in-theory (e/d* (translation-governing-addresses-for-same-1G-page
			     translation-governing-addresses-1G-pages-and-wb-to-page-dir-ptr-table-entry-addr
			     translation-governing-addresses
			     translation-governing-addresses-for-pml4-table
			     translation-governing-addresses-for-page-dir-ptr-table
			     pdpt-base-addr
			     pml4-table-base-addr)
			    (mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs-alt
			     subset-p
			     member-p
			     mv-nth-0-las-to-pas-subset-p
			     cdr-mv-nth-1-las-to-pas
			     mv-nth-0-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p
			     r-w-x-is-irrelevant-for-mv-nth-1-las-to-pas-when-no-errors
			     member-p-canonical-address-listp
			     mv-nth-1-las-to-pas-subset-p
			     car-create-canonical-address-list
			     consp-of-create-canonical-address-list
			     commutativity-of-+
			     remove-duplicate-keys
			     member-p-strip-cars-of-remove-duplicate-keys
			     pml4-table-entry-addr-to-c-program-optimized-form
			     page-dir-ptr-table-entry-addr-to-c-program-optimized-form
			     bitops::logand-with-negated-bitmask
			     force (force)
			     not
			     bitops::logand-with-negated-bitmask)))))

(defthmd all-translation-governing-addresses-1G-pages-and-wb-to-page-dir-ptr-table-entry-addr-general
  (implies
   (and
    (equal page-dir-ptr-table-entry-addr
	   (page-dir-ptr-table-entry-addr lin-addr (pdpt-base-addr lin-addr (double-rewrite x86))))
    (equal page-dir-ptr-table-entry
	   (combine-bytes
	    (mv-nth 1 (rb (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
			  :r (double-rewrite x86)))))
    (equal cpl (cpl x86))

    ;; PML4TE is direct-mapped.
    (direct-map-p
     8 (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86)))
     :r cpl (double-rewrite x86))
    (not
     (mv-nth
      0
      (las-to-pas
       (create-canonical-address-list
	8
	(pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86))))
       :r cpl (double-rewrite x86))))
    (disjoint-p$
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list
	8
	(pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86))))
       :r cpl (double-rewrite x86)))
     (all-translation-governing-addresses
      (create-canonical-address-list
       8
       (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86))))
      (double-rewrite x86)))

    ;; PDPTE is direct-mapped.
    (direct-map-p
     8 page-dir-ptr-table-entry-addr :r cpl (double-rewrite x86))
    (not
     (mv-nth
      0
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r cpl (double-rewrite x86))))
    (disjoint-p$
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r cpl (double-rewrite x86)))
     (all-translation-governing-addresses
      (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
      (double-rewrite x86)))

    ;; Physical addresses of PML4TE and PDPTE are disjoint.
    (disjoint-p$
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r cpl (double-rewrite x86)))
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 (pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)))
       :r cpl (double-rewrite x86))))
    ;; (disjoint-p (addr-range 8 (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86))))
    ;;             (addr-range 8 page-dir-ptr-table-entry-addr))

    (equal (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) (double-rewrite x86)))
	   (addr-range 8 page-dir-ptr-table-entry-addr))

    (disjoint-p
     (mv-nth 1
	     (las-to-pas
	      (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
	      :r cpl (double-rewrite x86)))
     (all-translation-governing-addresses (strip-cars addr-lst) (double-rewrite x86)))



    (equal (page-present page-dir-ptr-table-entry)
	   (page-present (combine-bytes (strip-cdrs addr-lst))))
    (equal (page-read-write page-dir-ptr-table-entry)
	   (page-read-write (combine-bytes (strip-cdrs addr-lst))))
    (equal (page-user-supervisor page-dir-ptr-table-entry)
	   (page-user-supervisor (combine-bytes (strip-cdrs addr-lst))))
    (equal (page-execute-disable page-dir-ptr-table-entry)
	   (page-execute-disable (combine-bytes (strip-cdrs addr-lst))))
    (equal (page-size page-dir-ptr-table-entry)
	   (page-size (combine-bytes (strip-cdrs addr-lst))))
    (equal (page-size page-dir-ptr-table-entry) 1)
    (equal (part-select page-dir-ptr-table-entry :low 13 :high 29)
	   (part-select (combine-bytes (strip-cdrs addr-lst)) :low 13 :high 29))

    (addr-byte-alistp addr-lst)
    (canonical-address-p (+ 7 (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86)))))
    (canonical-address-p (+ 7 page-dir-ptr-table-entry-addr))
    (canonical-address-p lin-addr)
    (canonical-address-p (+ -1 lin-addr m))
    (natp m)
    (<= m *2^30*)
    (natp iteration)
    (equal (loghead 30 lin-addr) 0)
    (not (programmer-level-mode x86))
    (x86p x86))
   (equal
    (all-translation-governing-addresses
     (create-canonical-address-list-alt iteration m lin-addr) (mv-nth 1 (wb addr-lst x86)))
    (all-translation-governing-addresses
     (create-canonical-address-list-alt iteration m lin-addr) x86)))
  :hints (("Goal"
	   :induct (create-canonical-address-list-alt iteration m lin-addr)
	   :do-not '(preprocess)
	   :in-theory (e/d* (all-translation-governing-addresses
			     translation-governing-addresses-for-same-1G-page
			     translation-governing-addresses-for-same-1G-page-and-wb-to-page-dir-ptr-table-entry-addr
			     translation-governing-addresses-1G-pages-and-wb-to-page-dir-ptr-table-entry-addr
			     all-translation-governing-addresses-1G-pages-general)
			    (member-p
			     subset-p
			     member-p-strip-cars-of-remove-duplicate-keys
			     page-dir-ptr-table-entry-addr-to-c-program-optimized-form
			     bitops::logand-with-negated-bitmask
			     force (force)
			     not)))))

(defthm all-translation-governing-addresses-1G-pages-and-wb-to-page-dir-ptr-table-entry-addr
  (implies
   (and
    ;; Restrict this rule so that it fires when lin-addr is either (XR
    ;; :RGF *RSI* X86) or (XR :RGF *RDI* X86) or lin-addr.
    (syntaxp (or
	      (eq lin-addr '(XR ':RGF '6 X86))
	      (eq lin-addr '(XR ':RGF '7 X86))
	      (eq lin-addr 'lin-addr)))
    (equal page-dir-ptr-table-entry-addr
	   (page-dir-ptr-table-entry-addr
	    lin-addr (pdpt-base-addr lin-addr (double-rewrite x86))))
    (equal page-dir-ptr-table-entry
	   (combine-bytes
	    (mv-nth
	     1
	     (rb (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
		 :r (double-rewrite x86)))))
    (equal cpl (cpl x86))
    (direct-map-p
     8
     (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86)))
     :r cpl (double-rewrite x86))
    (disjoint-p$
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list
	8
	(pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86))))
       :r cpl (double-rewrite x86)))
     (all-translation-governing-addresses
      (create-canonical-address-list
       8
       (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86))))
      (double-rewrite x86)))

    (direct-map-p 8 page-dir-ptr-table-entry-addr :r cpl (double-rewrite x86))
    (disjoint-p$
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r cpl (double-rewrite x86)))
     (all-translation-governing-addresses
      (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
      (double-rewrite x86)))
    (disjoint-p$
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r cpl (double-rewrite x86)))
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list
	8
	(pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86))))
       :r cpl (double-rewrite x86))))
    (equal
     (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) (double-rewrite x86)))
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r cpl (double-rewrite x86))))
    (disjoint-p
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r cpl (double-rewrite x86)))
     (all-translation-governing-addresses (strip-cars addr-lst) (double-rewrite x86)))

    (equal (page-present page-dir-ptr-table-entry)
	   (page-present (combine-bytes (strip-cdrs addr-lst))))
    (equal (page-read-write page-dir-ptr-table-entry)
	   (page-read-write (combine-bytes (strip-cdrs addr-lst))))
    (equal (page-user-supervisor page-dir-ptr-table-entry)
	   (page-user-supervisor (combine-bytes (strip-cdrs addr-lst))))
    (equal (page-execute-disable page-dir-ptr-table-entry)
	   (page-execute-disable (combine-bytes (strip-cdrs addr-lst))))
    (equal (page-size page-dir-ptr-table-entry)
	   (page-size (combine-bytes (strip-cdrs addr-lst))))
    (equal (page-size page-dir-ptr-table-entry) 1)
    (equal (part-select page-dir-ptr-table-entry :low 13 :high 29)
	   (part-select (combine-bytes (strip-cdrs addr-lst)) :low 13 :high 29))
    (addr-byte-alistp addr-lst)
    (canonical-address-p (+ 7 (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86)))))
    (canonical-address-p (+ 7 page-dir-ptr-table-entry-addr))
    (equal (loghead 30 lin-addr) 0)
    (canonical-address-p (+ -1 lin-addr m))
    (<= m *2^30*)
    (x86p x86))
   (equal
    (all-translation-governing-addresses
     (create-canonical-address-list m lin-addr) (mv-nth 1 (wb addr-lst x86)))
    (all-translation-governing-addresses
     (create-canonical-address-list m lin-addr) (double-rewrite x86))))
  :hints (("Goal"
	   :do-not-induct t
	   :do-not '(preprocess)
	   :use ((:instance all-translation-governing-addresses-1G-pages-and-wb-to-page-dir-ptr-table-entry-addr-general
			    (iteration 0)))
	   :in-theory (e/d* (create-canonical-address-list-alt-is-create-canonical-address-list
			     direct-map-p
			     las-to-pas)
			    (all-translation-governing-addresses
			     mv-nth-0-las-to-pas-subset-p
			     subset-p
			     mv-nth-0-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p
			     member-p
			     rewrite-rb-to-rb-alt
			     rb-and-rm-low-64-for-direct-map
			     translation-governing-addresses-for-same-1G-page
			     member-p-strip-cars-of-remove-duplicate-keys
			     page-dir-ptr-table-entry-addr-to-c-program-optimized-form
			     bitops::logand-with-negated-bitmask
			     force (force)
			     not)))))

;; ======================================================================

;; Begin proof of rb-values-1G-pages-and-wb-to-page-dir-ptr-table-entry-addr:

(defthm rb-values-1G-pages-and-wb-to-page-dir-ptr-table-entry-addr
  (implies
   (and
    (equal page-dir-ptr-table-entry-addr
	   (page-dir-ptr-table-entry-addr
	    lin-addr (pdpt-base-addr lin-addr (double-rewrite x86))))
    (equal page-dir-ptr-table-entry
	   (combine-bytes
	    (mv-nth
	     1
	     (rb (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
		 :r (double-rewrite x86)))))
    (equal cpl (cpl x86))

    (direct-map-p
     8 (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86)))
     :r cpl (double-rewrite x86))
    (not
     (mv-nth
      0
      (las-to-pas
       (create-canonical-address-list
	8
	(pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86))))
       :r cpl (double-rewrite x86))))
    (disjoint-p$
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list
	8
	(pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86))))
       :r cpl (double-rewrite x86)))
     (all-translation-governing-addresses
      (create-canonical-address-list
       8
       (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86))))
      (double-rewrite x86)))

    (direct-map-p 8 page-dir-ptr-table-entry-addr :r cpl (double-rewrite x86))
    (disjoint-p$
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r cpl (double-rewrite x86)))
     (all-translation-governing-addresses
      (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
      (double-rewrite x86)))
    (disjoint-p$
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r cpl (double-rewrite x86)))
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list
	8
	(pml4-table-entry-addr lin-addr (pml4-table-base-addr x86)))
       :r cpl (double-rewrite x86))))

    (equal
     (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) (double-rewrite x86)))
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r cpl (double-rewrite x86))))

    (disjoint-p
     (mv-nth
      1
      (las-to-pas
       (create-canonical-address-list 8 page-dir-ptr-table-entry-addr)
       :r cpl (double-rewrite x86)))
     (all-translation-governing-addresses (strip-cars addr-lst) (double-rewrite x86)))

    (not (mv-nth 0
		 (las-to-pas (create-canonical-address-list *2^30* lin-addr)
			     :r cpl (double-rewrite x86))))
    (disjoint-p$
     (addr-range
      *2^30*
      (ash (loghead 22 (logtail 30 (combine-bytes (strip-cdrs addr-lst))))
	   30))
     (open-qword-paddr-list
      (gather-all-paging-structure-qword-addresses (double-rewrite x86))))

    (disjoint-p
     (addr-range
      *2^30*
      (ash (loghead 22 (logtail 30 (combine-bytes (strip-cdrs addr-lst))))
	   30))
     (mv-nth 1 (las-to-pas (strip-cars addr-lst) :w (cpl x86) (double-rewrite x86))))

    (equal (page-present page-dir-ptr-table-entry)
	   (page-present (combine-bytes (strip-cdrs addr-lst))))
    (equal (page-read-write page-dir-ptr-table-entry)
	   (page-read-write (combine-bytes (strip-cdrs addr-lst))))
    (equal (page-user-supervisor page-dir-ptr-table-entry)
	   (page-user-supervisor (combine-bytes (strip-cdrs addr-lst))))
    (equal (page-execute-disable page-dir-ptr-table-entry)
	   (page-execute-disable (combine-bytes (strip-cdrs addr-lst))))
    (equal (page-size page-dir-ptr-table-entry)
	   (page-size (combine-bytes (strip-cdrs addr-lst))))
    (equal (page-size page-dir-ptr-table-entry) 1)
    (equal (part-select page-dir-ptr-table-entry :low 13 :high 29)
	   (part-select (combine-bytes (strip-cdrs addr-lst)) :low 13 :high 29))
    (addr-byte-alistp addr-lst)
    (canonical-address-p
     (+ 7 (pml4-table-entry-addr lin-addr (pml4-table-base-addr (double-rewrite x86)))))
    (canonical-address-p (+ 7 page-dir-ptr-table-entry-addr))
    (canonical-address-p lin-addr)
    (equal (loghead 30 lin-addr) 0)
    (not (programmer-level-mode x86))
    (x86p x86))
   (and
    (equal (mv-nth 0 (rb (create-canonical-address-list *2^30* lin-addr) :r (mv-nth 1 (wb addr-lst x86))))
	   nil)
    (equal (mv-nth 1 (rb
		      (create-canonical-address-list *2^30* lin-addr)
		      :r (mv-nth 1 (wb addr-lst x86))))
	   (read-from-physical-memory
	    (addr-range *2^30*
			(ash (loghead 22 (logtail 30 (combine-bytes (strip-cdrs addr-lst))))
			     30))
	    (double-rewrite x86)))))
  :hints (("Goal"
	   :do-not-induct t
	   :in-theory (e/d* (rb)
			    (subset-p
			     mv-nth-0-las-to-pas-subset-p
			     member-p
			     unsigned-byte-p-of-combine-bytes-and-rb-in-system-level-mode
			     unsigned-byte-p-of-combine-bytes
			     disjoint-p-subset-p
			     cdr-mv-nth-1-las-to-pas
			     mv-nth-0-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p
			     member-p-canonical-address-listp
			     member-p-strip-cars-of-remove-duplicate-keys
			     page-dir-ptr-table-entry-addr-to-c-program-optimized-form
			     bitops::logand-with-negated-bitmask
			     force (force)
			     not)))))

;; ======================================================================

(defun-nx source-data-preconditions (x86)
  (and
   ;; The physical addresses corresponding to destination
   ;; PDPTE are disjoint from the translation-governing
   ;; addresses of the source linear addresses.  Note
   ;; that this means that the destination PDPTE can't
   ;; serve as the PML4TE or PDPTE of the source.
   (disjoint-p
    (mv-nth
     1
     (las-to-pas
      (create-canonical-address-list
       8
       (page-dir-ptr-table-entry-addr
	(xr :rgf *rsi* x86)
	(pdpt-base-addr (xr :rgf *rsi* x86) x86)))
      :w (cpl x86) x86))
    (all-translation-governing-addresses
     (create-canonical-address-list *2^30* (xr :rgf *rdi* x86))
     x86))

   ;; The physical addresses corresponding to destination
   ;; PDPTE are disjoint from the source physical
   ;; addresses.
   (disjoint-p
    (mv-nth
     1
     (las-to-pas
      (create-canonical-address-list
       8
       (page-dir-ptr-table-entry-addr
	(xr :rgf *rsi* x86)
	(pdpt-base-addr (xr :rgf *rsi* x86) x86)))
      :w (cpl x86) x86))
    (mv-nth 1
	    (las-to-pas (create-canonical-address-list *2^30* (xr :rgf *rdi* x86))
			:r (cpl x86) x86)))

   ;; The stack is disjoint from the source physical
   ;; addresses.
   (disjoint-p
    (mv-nth
     1
     (las-to-pas
      (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86)))
      :w (cpl x86) x86))
    (mv-nth 1
	    (las-to-pas (create-canonical-address-list *2^30* (xr :rgf *rdi* x86))
			:r (cpl x86) x86)))
   ;; Source physical addresses are disjoint from the paging
   ;; structures' physical addresses.
   (disjoint-p$
    (mv-nth
     1
     (las-to-pas (create-canonical-address-list *2^30* (xr :rgf *rdi* x86))
		 :r (cpl x86) x86))
    (open-qword-paddr-list
     (gather-all-paging-structure-qword-addresses x86)))
   ;; The source PDPTE physical addresses are disjoint from
   ;; the source PML4TE physical addresses.
   (disjoint-p$
    (mv-nth 1
	    (las-to-pas (create-canonical-address-list
			 8
			 (page-dir-ptr-table-entry-addr
			  (xr :rgf *rdi* x86)
			  (pdpt-base-addr (xr :rgf *rdi* x86) x86)))
			:r 0 x86))
    (mv-nth
     1
     (las-to-pas
      (create-canonical-address-list
       8
       (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86)))
      :r 0 x86)))
   ;; Source PML4TE is direct-mapped.
   (direct-map-p
    8 (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86))
    :r 0 x86)
   ;; Source PDPTE is direct-mapped.
   (direct-map-p
    8 (page-dir-ptr-table-entry-addr
       (xr :rgf *rdi* x86) (pdpt-base-addr (xr :rgf *rdi* x86) x86))
    :r 0 x86)))

(defthmd source-data-from-initial-state-in-terms-of-read-from-physical-memory-and-addr-range
  (implies (and (rewire_dst_to_src-effects-preconditions x86)
		(source-data-preconditions x86))
	   (equal
	    (mv-nth 1 (rb (create-canonical-address-list *2^30* (xr :rgf *rdi* x86))
			  :r x86))
	    (read-from-physical-memory
	     (addr-range
	      *2^30* (ash (loghead 22
				   (logtail
				    30
				    (rm-low-64
				     (page-dir-ptr-table-entry-addr
				      (xr :rgf *rdi* x86)
				      (pdpt-base-addr (xr :rgf *rdi* x86) x86))
				     x86)))
			  30))
	     x86)))
  :hints (("Goal"
	   :do-not-induct t
	   :in-theory (e/d*
		       (page-size
			las-to-pas-values-for-same-1G-page
			source-data-from-initial-state-in-terms-of-read-from-physical-memory-and-las-to-pas)
		       (subset-p
			member-p
			mv-nth-0-las-to-pas-subset-p
			mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs-alt
			two-mv-nth-1-las-to-pas-subset-p-disjoint-from-las-to-pas
			len-of-rb-in-system-level-mode
			rewrite-rb-to-rb-alt
			page-dir-ptr-table-entry-addr-to-c-program-optimized-form
			unsigned-byte-p-52-of-left-shifting-a-40-bit-vector-by-12
			unsigned-byte-p-of-combine-bytes-and-rb-in-system-level-mode
			mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs
			(:meta acl2::mv-nth-cons-meta)
			create-canonical-address-list
			mv-nth-0-las-to-pas-subset-p-with-l-addrs-from-bind-free
			acl2::loghead-identity)))))

;; ======================================================================

;; Now back to proving destination-data-from-final-state:

;; (acl2::why all-translation-governing-addresses-and-mv-nth-1-wb-disjoint)
;; (acl2::why rb-wb-disjoint-in-system-level-mode)
;; (acl2::why pdpt-base-addr-after-mv-nth-1-wb)
;; (acl2::why la-to-pas-values-and-mv-nth-1-wb-disjoint-from-xlation-gov-addrs)
;; (acl2::why las-to-pas-values-1G-pages-and-wb-to-page-dir-ptr-table-entry-addr)
;; (acl2::why all-translation-governing-addresses-1G-pages-and-wb-to-page-dir-ptr-table-entry-addr)
;; (acl2::why rb-values-1G-pages-and-wb-to-page-dir-ptr-table-entry-addr)
;; (acl2::why mv-nth-1-rb-after-mv-nth-2-las-to-pas)

(defun-nx destination-data-preconditions (x86)
  (and
   ;; Source PML4TE is direct-mapped.
   (direct-map-p
    8
    (pml4-table-entry-addr (xr :rgf *rdi* x86) (pml4-table-base-addr x86))
    :r (cpl x86) x86)
   ;; Source PDPTE is direct-mapped.
   (direct-map-p
    8
    (page-dir-ptr-table-entry-addr (xr :rgf *rdi* x86)
				   (pdpt-base-addr (xr :rgf *rdi* x86) x86))
    :r (cpl x86) x86)
   ;; Destination PML4TE is direct-mapped.
   (direct-map-p 8
		 (pml4-table-entry-addr (xr :rgf *rsi* x86)
					(pml4-table-base-addr x86))
		 :r (cpl x86) x86)

   ;; The destination PML4TE physical addresses are disjoint from the
   ;; translation-governing addresses of the destination PDPTE.
   (disjoint-p
    (mv-nth
     1
     (las-to-pas (create-canonical-address-list
		  8
		  (pml4-table-entry-addr (xr :rgf *rsi* x86)
					 (pml4-table-base-addr x86)))
		 :r (cpl x86) x86))
    (all-translation-governing-addresses
     (create-canonical-address-list
      8
      (page-dir-ptr-table-entry-addr (xr :rgf *rsi* x86)
				     (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
     x86))
   ;; Destination PDPTE physical addresses are disjoint from the
   ;; destination PML4TE physical addresses.
   (disjoint-p$
    (mv-nth
     1
     (las-to-pas (create-canonical-address-list
		  8
		  (page-dir-ptr-table-entry-addr
		   (xr :rgf *rsi* x86)
		   (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
		 :w (cpl x86) x86))
    (mv-nth
     1
     (las-to-pas
      (create-canonical-address-list
       8
       (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86)))
      :r (cpl x86) x86)))


   ;; The source physical addresses are disjoint from the stack physical addresses.
   (disjoint-p
    (addr-range
     *2^30*
     (ash (loghead 22
		   (logtail 30
			    (rm-low-64 (page-dir-ptr-table-entry-addr
					(xr :rgf *rdi* x86)
					(pdpt-base-addr (xr :rgf *rdi* x86) x86)) x86)))
	  30))
    (mv-nth
     1
     (las-to-pas (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86))) :w (cpl x86) x86)))

   ;; The source physical addresses are disjoint from all the paging
   ;; structure physical addresses.
   (disjoint-p$
    (addr-range
     *2^30*
     (ash (loghead 22
		   (logtail
		    30
		    (rm-low-64 (page-dir-ptr-table-entry-addr
				(xr :rgf *rdi* x86)
				(pdpt-base-addr (xr :rgf *rdi* x86) x86)) x86)))
	  30))
    (open-qword-paddr-list (gather-all-paging-structure-qword-addresses x86)))))

(defun-nx throwaway-destination-data-preconditions (x86)
  (and
   ;; This should follow from the hyp about direct map of destination
   ;; PDPTE, and that the source physical addresses are disjoint from
   ;; all the paging structure physical addresses.
   (disjoint-p
    (addr-range
     *2^30*
     (ash (loghead 22
		   (logtail
		    30
		    (rm-low-64 (page-dir-ptr-table-entry-addr
				(xr :rgf *rdi* x86)
				(pdpt-base-addr (xr :rgf *rdi* x86) x86)) x86)))
	  30))
    (addr-range
     8 (page-dir-ptr-table-entry-addr
	(xr :rgf *rsi* x86)
	(pdpt-base-addr (xr :rgf *rsi* x86) x86))))

   ;; This should follow from
   ;; destination-PDPTE-and-destination-PML4TE-no-interfere-p
   ;; (disjoint-p$ issue) and direct map of destination PDPTE.
   (disjoint-p
    (addr-range 8
		(page-dir-ptr-table-entry-addr
		 (xr :rgf *rsi* x86)
		 (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
    (all-translation-governing-addresses
     (create-canonical-address-list
      8
      (pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86))) x86))

   ;; This should follow from
   ;; destination-PDPTE-and-source-PML4E-no-interfere-p (disjoint-p$
   ;; issue) and direct map of destination PDPTE.
   (disjoint-p
    (addr-range 8
		(page-dir-ptr-table-entry-addr
		 (xr :rgf *rsi* x86)
		 (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
    (all-translation-governing-addresses
     (create-canonical-address-list
      8
      (pml4-table-entry-addr (xr :rgf *rdi* x86)
			     (pml4-table-base-addr x86)))
     x86))

   ;; This should follow from
   ;; destination-PDPTE-and-source-PDPTE-no-interfere-p (disjoint-p$
   ;; issue) and direct map of destination PDPTE.
   (disjoint-p
    (addr-range 8
		(page-dir-ptr-table-entry-addr
		 (xr :rgf *rsi* x86)
		 (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
    (all-translation-governing-addresses
     (create-canonical-address-list
      8
      (page-dir-ptr-table-entry-addr
       (xr :rgf *rdi* x86)
       (pdpt-base-addr (xr :rgf *rdi* x86) x86)))
     x86))

   ;; disjoint-p$ issue
   ;; Follows from destination-PML4TE-ok-p.
   (disjoint-p
    (mv-nth
     1
     (las-to-pas
      (create-canonical-address-list
       8
       (pml4-table-entry-addr (xr :rgf *rsi* x86)
			      (pml4-table-base-addr x86)))
      :r (cpl x86) x86))
    (all-translation-governing-addresses
     (create-canonical-address-list
      8
      (pml4-table-entry-addr (xr :rgf *rsi* x86)
			     (pml4-table-base-addr x86)))
     x86))

   ;; disjoint-p$ issue
   ;; Follows from destination-PML4TE-and-source-PDPTE-no-interfere-p.
   (disjoint-p
    (mv-nth
     1
     (las-to-pas
      (create-canonical-address-list
       8
       (pml4-table-entry-addr (xr :rgf *rsi* x86)
			      (pml4-table-base-addr x86)))
      :r (cpl x86) x86))
    (all-translation-governing-addresses
     (create-canonical-address-list
      8
      (page-dir-ptr-table-entry-addr
       (xr :rgf *rdi* x86)
       (pdpt-base-addr (xr :rgf *rdi* x86) x86)))
     x86))

   ;; disjoint-p$ issue
   ;; Follows from destination-PML4TE-and-source-PML4TE-no-interfere-p.
   (disjoint-p
    (mv-nth
     1
     (las-to-pas
      (create-canonical-address-list
       8
       (pml4-table-entry-addr (xr :rgf *rsi* x86)
			      (pml4-table-base-addr x86)))
      :r (cpl x86) x86))
    (all-translation-governing-addresses
     (create-canonical-address-list
      8
      (pml4-table-entry-addr (xr :rgf *rdi* x86)
			     (pml4-table-base-addr x86)))
     x86))


   ;; disjoint-p$ issue
   ;; Follows from destination-PML4TE-and-stack-no-interfere-p.
   (disjoint-p
    (mv-nth
     1
     (las-to-pas
      (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86))) :w (cpl x86) x86))
    (mv-nth
     1
     (las-to-pas (create-canonical-address-list
		  8
		  (pml4-table-entry-addr (xr :rgf *rsi* x86)
					 (pml4-table-base-addr x86)))
		 :r (cpl x86) x86)))

   ;; disjoint-p$ issue
   ;; Follows from destination-PDPTE-and-stack-no-interfere-p.
   (disjoint-p
    (mv-nth
     1
     (las-to-pas
      (create-canonical-address-list 8 (+ -24 (xr :rgf *rsp* x86)))
      :w (cpl x86) x86))
    (mv-nth
     1
     (las-to-pas
      (create-canonical-address-list
       8
       (page-dir-ptr-table-entry-addr (xr :rgf *rsi* x86)
				      (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
      :r (cpl x86) x86)))))

(local
 (defthmd destination-pdpte-is-in-all-paging-structures
   (implies (and
	     (x86-state-okp x86)
	     (destination-addresses-ok-p x86)
	     (destination-pml4te-ok-p x86)
	     (direct-map-p
	      8
	      (pml4-table-entry-addr (xr :rgf *rsi* x86)
				     (pml4-table-base-addr x86))
	      :r (cpl x86) x86))
	    (subset-p
	     (addr-range
	      8 (page-dir-ptr-table-entry-addr
		 (xr :rgf *rsi* x86)
		 (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
	     (open-qword-paddr-list (gather-all-paging-structure-qword-addresses x86))))
   :hints (("Goal"
	    :hands-off (disjoint-p)
	    :in-theory (e/d* (direct-map-p pdpt-base-addr page-size)
			     (page-dir-ptr-table-entry-addr
			      page-dir-ptr-table-entry-addr-to-c-program-optimized-form
			      canonical-address-p-page-dir-ptr-table-entry-addr-to-c-program-optimized-form))))))

(local
 (defthmd throwaway-destination-data-preconditions-lemma-helper
   (implies (and
	     (x86-state-okp x86)
	     (destination-addresses-ok-p x86)
	     (destination-pml4te-ok-p x86)
	     (direct-map-p
	      8
	      (pml4-table-entry-addr (xr :rgf *rsi* x86)
				     (pml4-table-base-addr x86))
	      :r (cpl x86) x86)
	     (disjoint-p$
	      (addr-range
	       *2^30*
	       (ash (loghead 22
			     (logtail
			      30
			      (rm-low-64 (page-dir-ptr-table-entry-addr
					  (xr :rgf *rdi* x86)
					  (pdpt-base-addr (xr :rgf *rdi* x86) x86)) x86)))
		    30))
	      (open-qword-paddr-list (gather-all-paging-structure-qword-addresses x86))))
	    (disjoint-p
	     (addr-range
	      *2^30*
	      (ash (loghead 22
			    (logtail
			     30
			     (rm-low-64 (page-dir-ptr-table-entry-addr
					 (xr :rgf *rdi* x86)
					 (pdpt-base-addr (xr :rgf *rdi* x86) x86)) x86)))
		   30))
	     (addr-range
	      8 (page-dir-ptr-table-entry-addr
		 (xr :rgf *rsi* x86)
		 (pdpt-base-addr (xr :rgf *rsi* x86) x86)))))
   :hints (("Goal"
	    :hands-off (disjoint-p)
	    :use ((:instance destination-pdpte-is-in-all-paging-structures)
		  (:instance disjoint-p-subset-p
			     (x (addr-range
				 *2^30*
				 (ash (loghead 22
					       (logtail
						30
						(rm-low-64 (page-dir-ptr-table-entry-addr
							    (xr :rgf *rdi* x86)
							    (pdpt-base-addr (xr :rgf *rdi* x86) x86)) x86)))
				      30)))
			     (y (open-qword-paddr-list (gather-all-paging-structure-qword-addresses x86)))
			     (a (addr-range
				 *2^30*
				 (ash (loghead 22
					       (logtail
						30
						(rm-low-64 (page-dir-ptr-table-entry-addr
							    (xr :rgf *rdi* x86)
							    (pdpt-base-addr (xr :rgf *rdi* x86) x86)) x86)))
				      30)))
			     (b (addr-range
				 8 (page-dir-ptr-table-entry-addr
				    (xr :rgf *rsi* x86)
				    (pdpt-base-addr (xr :rgf *rsi* x86) x86))))))
	    :in-theory (e/d* (disjoint-p$
			      subset-p)
			     (disjoint-p-subset-p
			      page-dir-ptr-table-entry-addr
			      page-dir-ptr-table-entry-addr-to-c-program-optimized-form
			      canonical-address-p-page-dir-ptr-table-entry-addr-to-c-program-optimized-form))))))

(local
 (defthmd throwaway-destination-data-preconditions-lemma
   (implies (and (rewire_dst_to_src-effects-preconditions x86)
		 (destination-data-preconditions x86))
	    (throwaway-destination-data-preconditions x86))
   :hints (("Goal"
	    :hands-off (disjoint-p)
	    :use ((:instance throwaway-destination-data-preconditions-lemma-helper))
	    :in-theory (e/d* (direct-map-p
			      disjoint-p$)
			     ((:rewrite mv-nth-0-las-to-pas-subset-p)
			      (:definition subset-p)
			      (:rewrite mv-nth-0-las-to-pas-subset-p-with-l-addrs-from-bind-free)
			      (:rewrite len-of-rb-in-system-level-mode)
			      (:rewrite acl2::loghead-identity)
			      (:definition member-p)
			      (:rewrite page-dir-ptr-table-entry-addr-to-c-program-optimized-form)
			      (:rewrite subset-p-two-create-canonical-address-lists-general)
			      (:rewrite unsigned-byte-p-of-combine-bytes)
			      (:rewrite member-p-canonical-address-listp)
			      (:linear adding-7-to-page-dir-ptr-table-entry-addr)
			      (:rewrite greater-logbitp-of-unsigned-byte-p . 2)
			      (:linear *physical-address-size*p-page-dir-ptr-table-entry-addr)
			      (:linear size-of-combine-bytes)
			      (:linear unsigned-byte-p-of-combine-bytes)
			      (:rewrite cdr-create-canonical-address-list)
			      (:definition no-duplicates-p)
			      (:rewrite consp-mv-nth-1-las-to-pas)
			      (:rewrite member-p-of-not-a-consp)
			      (:definition create-canonical-address-list)
			      (:rewrite loghead-of-non-integerp)
			      (:rewrite default-+-2)
			      (:type-prescription acl2::|x < y  =>  0 < -x+y|)
			      (:rewrite acl2::equal-of-booleans-rewrite)
			      (:linear rgfi-is-i64p . 2)
			      (:linear rip-is-i48p . 2)
			      (:rewrite bitops::unsigned-byte-p-when-unsigned-byte-p-less)
			      (:rewrite loghead-negative)
			      (:linear rip-is-i48p . 1)
			      (:type-prescription subset-p)
			      (:rewrite default-+-1)
			      (:linear rgfi-is-i64p . 1)
			      (:type-prescription member-p)
			      (:rewrite default-<-2)
			      (:type-prescription pdpt-base-addr)
			      (:rewrite default-<-1)
			      (:rewrite consp-of-create-canonical-address-list)
			      (:rewrite car-create-canonical-address-list)
			      (:meta acl2::cancel_plus-equal-correct)
			      (:meta acl2::cancel_times-equal-correct)
			      (:rewrite canonical-address-p-limits-thm-3)
			      (:rewrite subset-p-cdr-y)
			      (:rewrite member-p-cdr)
			      (:rewrite canonical-address-p-limits-thm-2)
			      (:meta acl2::cancel_plus-lessp-correct)
			      (:rewrite open-mv-nth-1-las-to-pas-for-same-1g-page-general-1)
			      (:rewrite canonical-address-p-limits-thm-0)
			      (:linear adding-7-to-pml4-table-entry-addr)
			      (:rewrite acl2::consp-when-member-equal-of-atom-listp)
			      (:rewrite member-p-of-subset-is-member-p-of-superset)
			      (:type-prescription adding-7-to-page-dir-ptr-table-entry-addr)
			      (:rewrite canonical-address-p-limits-thm-1)
			      (:rewrite member-p-and-mult-8-qword-paddr-listp)
			      (:rewrite default-cdr)
			      (:rewrite default-car)
			      (:linear *physical-address-size*p-pml4-table-entry-addr)
			      (:type-prescription booleanp)
			      (:rewrite subset-p-cdr-x)
			      (:linear ash-monotone-2)
			      (:rewrite rationalp-implies-acl2-numberp)
			      (:type-prescription consp-mv-nth-1-las-to-pas)
			      (:rewrite acl2::ash-0)
			      (:rewrite cdr-mv-nth-1-las-to-pas)
			      (:rewrite acl2::equal-constant-+)
			      (:definition combine-bytes)
			      (:type-prescription adding-7-to-pml4-table-entry-addr)
			      (:rewrite
			       mv-nth-0-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p)
			      (:rewrite acl2::zip-open)
			      (:type-prescription len)
			      (:rewrite rb-and-rm-low-64-for-direct-map)
			      (:rewrite car-mv-nth-1-las-to-pas)
			      (:definition open-qword-paddr-list)
			      (:rewrite rewrite-rb-to-rb-alt)
			      (:rewrite len-of-create-canonical-address-list)
			      (:definition addr-range)
			      (:definition byte-listp)
			      (:rewrite acl2::member-of-cons)
			      (:definition binary-append)
			      (:rewrite acl2::ifix-when-not-integerp)
			      (:definition len)
			      (:meta acl2::mv-nth-cons-meta)
			      (:linear acl2::expt->-1)
			      (:rewrite acl2::append-when-not-consp)
			      (:type-prescription bitops::ash-natp-type)
			      (:linear member-p-pos-value)
			      (:linear member-p-pos-1-value)
			      (:linear acl2::index-of-<-len)
			      (:rewrite
			       mv-nth-1-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p)
			      (:definition n08p$inline)
			      (:rewrite mv-nth-1-las-to-pas-when-error)
			      (:rewrite commutativity-of-+)
			      (:linear mv-nth-1-idiv-spec)
			      (:linear mv-nth-1-div-spec)
			      (:rewrite neg-addr-range=nil)
			      (:rewrite bitops::logbitp-nonzero-of-bit)
			      (:rewrite right-shift-to-logtail)
			      (:type-prescription combine-bytes)
			      (:type-prescription ifix)
			      (:rewrite car-addr-range)
			      (:type-prescription zip)
			      (:type-prescription gather-all-paging-structure-qword-addresses)
			      (:rewrite unsigned-byte-p-of-logtail)
			      (:rewrite unsigned-byte-p-of-combine-bytes-and-rb-in-system-level-mode)
			      (:linear combine-bytes-size-for-rm64-programmer-level-mode)
			      (:rewrite acl2::subsetp-member . 2)
			      (:rewrite acl2::subsetp-member . 1)
			      (:rewrite acl2::logtail-identity)
			      (:rewrite cdr-addr-range)
			      (:rewrite ia32e-la-to-pa-in-programmer-level-mode)
			      (:rewrite canonical-address-p-rip)
			      (:type-prescription n64p-rm-low-64)
			      (:rewrite
			       mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures)
			      (:rewrite mv-nth-1-ia32e-la-to-pa-when-error)
			      (:rewrite bitops::logbitp-when-bitmaskp)
			      (:type-prescription signed-byte-p)
			      (:type-prescription n52p-mv-nth-1-ia32e-la-to-pa)
			      (:rewrite acl2::logext-identity)
			      (:rewrite open-mv-nth-0-las-to-pas-for-same-1g-page-general-2)
			      (:rewrite acl2::expt-with-violated-guards)
			      (:rewrite no-duplicates-p-and-append)
			      (:type-prescription bitp)
			      (:type-prescription acl2::bitmaskp$inline)
			      (:rewrite loghead-30-of-1g-aligned-lin-addr-+-n-2)
			      (:rewrite rm-low-64-in-programmer-level-mode)
			      (:type-prescription natp)
			      (:rewrite bitops::signed-byte-p-when-unsigned-byte-p-smaller)
			      (:rewrite bitops::signed-byte-p-when-signed-byte-p-smaller)
			      (:rewrite bitops::signed-byte-p-monotonicity)
			      (:type-prescription member-equal)
			      (:linear acl2::expt-is-increasing-for-base>1)
			      (:definition member-equal)
			      (:rewrite subset-p-cons-member-p-lemma)
			      (:rewrite r-w-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-when-no-errors)
			      (:rewrite not-member-p-when-disjoint-p)
			      (:rewrite member-p-start-rip-of-create-canonical-address-list)
			      (:rewrite bitops::normalize-logbitp-when-mods-equal)
			      (:rewrite bitops::logbitp-of-negative-const)
			      (:rewrite bitops::logbitp-of-mask)
			      (:rewrite bitops::logbitp-of-const)
			      (:rewrite greater-logbitp-of-unsigned-byte-p . 1)
			      (:meta bitops::open-logbitp-of-const-lite-meta)
			      (:rewrite
			       xlate-equiv-structures-and-logtail-30-rm-low-64-with-page-dir-ptr-table-entry-addr)
			      (:rewrite
			       all-mem-except-paging-structures-equal-aux-and-rm-low-64-from-rest-of-memory)
			      (:rewrite
			       all-mem-except-paging-structures-equal-and-rm-low-64-from-rest-of-memory)
			      (:linear bitops::expt-2-lower-bound-by-logbitp)))))))

(defthmd pdpte-base-addr-from-final-state-helper
  (implies (and
	    (rewire_dst_to_src-effects-preconditions x86)
	    (throwaway-destination-data-preconditions x86)
	    (destination-data-preconditions x86))

	   (equal
	    (pdpt-base-addr
	     (xr :rgf *rsi* x86)
	     (mv-nth
	      2
	      (las-to-pas
	       (create-canonical-address-list 6
					      (+ 184 (xr :rip 0 x86)))
	       :x
	       0
	       (mv-nth
		2
		(las-to-pas
		 (create-canonical-address-list
		  8
		  (page-dir-ptr-table-entry-addr
		   (xr :rgf *rsi* x86)
		   (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
		 :r
		 0
		 (mv-nth
		  2
		  (las-to-pas
		   (create-canonical-address-list 40
						  (+ 144 (xr :rip 0 x86)))
		   :x
		   0
		   (mv-nth
		    2
		    (las-to-pas
		     (create-canonical-address-list
		      3
		      (+ 140 (xr :rip 0 x86)))
		     :x
		     0
		     (mv-nth
		      2
		      (las-to-pas
		       (create-canonical-address-list
			8
			(pml4-table-entry-addr (xr :rgf *rsi* x86)
					       (pml4-table-base-addr x86)))
		       :r
		       0
		       (mv-nth
			2
			(las-to-pas
			 (create-canonical-address-list
			  32
			  (+ 108 (xr :rip 0 x86)))
			 :x
			 0
			 (mv-nth
			  2
			  (las-to-pas
			   (create-canonical-address-list
			    18
			    (+ 86 (xr :rip 0 x86)))
			   :x
			   0
			   (mv-nth
			    2
			    (las-to-pas
			     (create-canonical-address-list
			      8
			      (page-dir-ptr-table-entry-addr
			       (xr :rgf *rdi* x86)
			       (pdpt-base-addr (xr :rgf *rdi* x86) x86)))
			     :r
			     0
			     (mv-nth
			      2
			      (las-to-pas
			       (create-canonical-address-list
				40
				(+ 46 (xr :rip 0 x86)))
			       :x
			       0
			       (mv-nth
				2
				(las-to-pas
				 (create-canonical-address-list
				  4
				  (+ 38 (xr :rip 0 x86)))
				 :x
				 0
				 (mv-nth
				  2
				  (las-to-pas
				   (create-canonical-address-list
				    8
				    (pml4-table-entry-addr
				     (xr :rgf *rdi* x86)
				     (pml4-table-base-addr x86)))
				   :r
				   0
				   (mv-nth
				    2
				    (las-to-pas
				     (create-canonical-address-list
				      25
				      (+ 13 (xr :rip 0 x86)))
				     :x
				     0
				     (mv-nth
				      2
				      (las-to-pas
				       (create-canonical-address-list
					8
					(+ -24 (xr :rgf *rsp* x86)))
				       :r
				       0
				       (mv-nth
					2
					(las-to-pas
					 (create-canonical-address-list
					  5
					  (+ 8 (xr :rip 0 x86)))
					 :x
					 0
					 (mv-nth
					  1
					  (wb
					   (create-addr-bytes-alist
					    (create-canonical-address-list
					     8
					     (+ -24 (xr :rgf *rsp* x86)))
					    (byte-ify 8 (xr :ctr 3 x86)))
					   (mv-nth
					    2
					    (las-to-pas
					     (create-canonical-address-list
					      8
					      (xr :rip 0 x86))
					     :x
					     0
					     x86)))))))))))))))))))))))))))))))))
	    (pdpt-base-addr
	     (xr :rgf *rsi* x86)
	     x86)))
  :hints (("Goal"
	   :in-theory (e/d*
		       (page-size
			pml4-table-base-addr-from-final-state
			destination-pdpt-base-addr-from-final-state

			source-pml4-table-entry-from-final-state
			source-pdpt-base-addr-from-final-state
			source-addresses-from-final-state
			destination-pdpt-base-addr-from-final-state
			destination-pml4-table-entry-from-final-state
			disjoint-p-all-translation-governing-addresses-subset-p
			pdpt-base-addr)

		       (rewire_dst_to_src-disable


			read-from-physical-memory
			rewrite-rb-to-rb-alt
			page-dir-ptr-table-entry-addr-to-c-program-optimized-form
			unsigned-byte-p-52-of-left-shifting-a-40-bit-vector-by-12
			(:meta acl2::mv-nth-cons-meta)

			(:rewrite mv-nth-0-las-to-pas-subset-p)
			(:rewrite mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs-alt)
			(:definition subset-p)
			(:rewrite mv-nth-0-las-to-pas-subset-p-with-l-addrs-from-bind-free)
			(:rewrite member-p-canonical-address-listp)
			(:rewrite two-mv-nth-1-las-to-pas-subset-p-disjoint-from-las-to-pas)
			(:rewrite mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs)
			(:type-prescription member-p)
			(:rewrite open-mv-nth-1-las-to-pas-for-same-1g-page-general-1)
			(:rewrite acl2::loghead-identity)
			(:definition create-canonical-address-list)
			(:rewrite r/x-is-irrelevant-for-mv-nth-2-las-to-pas-when-no-errors)
			(:rewrite mv-nth-2-las-to-pas-system-level-non-marking-mode)
			(:rewrite canonical-address-p-rip)
			(:rewrite xr-page-structure-marking-mode-mv-nth-2-las-to-pas)
			(:rewrite combine-mv-nth-2-las-to-pas-same-r-w-x-when-addresses-in-sequence)
			(:definition int-lists-in-seq-p)
			(:rewrite rm-low-64-in-programmer-level-mode)
			(:rewrite right-shift-to-logtail)
			(:rewrite
			 all-mem-except-paging-structures-equal-aux-and-rm-low-64-from-rest-of-memory)
			(:rewrite
			 all-mem-except-paging-structures-equal-and-rm-low-64-from-rest-of-memory)
			(:rewrite
			 xlate-equiv-structures-and-logtail-12-rm-low-64-with-pml4-table-entry-addr)
			(:type-prescription member-p-physical-address-p-physical-address-listp)
			(:type-prescription acl2::|x < y  =>  0 < y-x|)
			(:rewrite
			 mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures)
			(:type-prescription member-p-physical-address-p)
			(:rewrite xr-page-structure-marking-mode-mv-nth-1-wb)
			(:rewrite acl2::cdr-of-append-when-consp)
			(:type-prescription binary-append)
			(:rewrite
			 all-translation-governing-addresses-1g-pages-and-wb-to-page-dir-ptr-table-entry-addr)
			(:rewrite
			 int-lists-in-seq-p-and-append-with-create-canonical-address-list-2)
			(:rewrite greater-logbitp-of-unsigned-byte-p . 2)
			(:rewrite acl2::consp-of-append)
			(:type-prescription int-lists-in-seq-p)
			(:rewrite int-lists-in-seq-p-and-append)
			(:rewrite acl2::car-of-append)
			(:linear n64p-rm-low-64)
			(:rewrite bitops::logand-with-bitmask)
			(:rewrite acl2::right-cancellation-for-+)
			(:rewrite
			 canonical-address-p-pml4-table-entry-addr-to-c-program-optimized-form)
			(:type-prescription acl2::bitmaskp$inline)
			(:rewrite unsigned-byte-p-of-combine-bytes-and-rb-in-system-level-mode)
			(:rewrite open-mv-nth-0-las-to-pas-for-same-1g-page-general-2)
			(:rewrite loghead-30-of-1g-aligned-lin-addr-+-n-2)
			(:rewrite ctri-is-n64p))))))

(def-gl-export entry-attributes-unchanged-when-destination-PDPTE-modified
  :hyp (and (unsigned-byte-p 64 dest-pdpte)
	    (unsigned-byte-p 64 src-pdpte))
  :concl (and
	  (equal (page-present (logior (logand 18442240475155922943 dest-pdpte)
				       (logand 4503598553628672 src-pdpte)))
		 (page-present dest-pdpte))
	  (equal (page-read-write (logior (logand 18442240475155922943 dest-pdpte)
					  (logand 4503598553628672 src-pdpte)))
		 (page-read-write dest-pdpte))
	  (equal (page-user-supervisor (logior (logand 18442240475155922943 dest-pdpte)
					       (logand 4503598553628672 src-pdpte)))
		 (page-user-supervisor dest-pdpte))
	  (equal (page-execute-disable (logior (logand 18442240475155922943 dest-pdpte)
					       (logand 4503598553628672 src-pdpte)))
		 (page-execute-disable dest-pdpte))
	  (equal (page-size (logior (logand 18442240475155922943 dest-pdpte)
				    (logand 4503598553628672 src-pdpte)))
		 (page-size dest-pdpte)))
  :g-bindings
  (gl::auto-bindings (:mix (:nat src-pdpte 64) (:nat dest-pdpte 64))))

(defthm pml4-table-base-addr-and-mv-nth-2-las-to-pas
  ;; I shouldn't need this lemma --- this should follow directly from
  ;; xlate-equiv-memory-and-pml4-table-base-addr and
  ;; xlate-equiv-memory-with-mv-nth-2-las-to-pas.
  (equal (pml4-table-base-addr (mv-nth 2 (las-to-pas l-addrs r-w-x cpl x86)))
	 (pml4-table-base-addr (double-rewrite x86))))

(defthmd destination-data-from-final-state-in-terms-of-read-from-physical-memory-and-addr-range
  (implies
   (and (rewire_dst_to_src-effects-preconditions x86)
	(throwaway-destination-data-preconditions x86)
	(destination-data-preconditions x86))
   (equal
    (mv-nth
     1
     (rb
      (create-canonical-address-list *2^30* (xr :rgf *rsi* x86))
      :r
      (x86-run (rewire_dst_to_src-clk) x86)))
    (read-from-physical-memory
     (addr-range
      *2^30*
      (ash
       (loghead
	22
	(logtail
	 30
	 (rm-low-64
	  (page-dir-ptr-table-entry-addr (xr :rgf *rdi* x86)
					 (pdpt-base-addr (xr :rgf *rdi* x86) x86))
	  x86)))
       30))
     x86)))
  :hints
  (("Goal"
    :use ((:instance rewire_dst_to_src-effects))
    :hands-off (x86-run)
    :in-theory
    (e/d*
     (pdpte-base-addr-from-final-state-helper
      direct-map-p
      page-size
      pml4-table-base-addr-from-final-state
      destination-pdpt-base-addr-from-final-state
      source-pml4-table-entry-from-final-state
      source-pdpt-base-addr-from-final-state
      source-addresses-from-final-state
      destination-pdpt-base-addr-from-final-state
      destination-pml4-table-entry-from-final-state
      disjoint-p-all-translation-governing-addresses-subset-p)
     (rewire_dst_to_src-disable
      read-from-physical-memory
      pdpt-base-addr-after-mv-nth-2-las-to-pas
      xw-xw-intra-simple-field-shadow-writes
      rewrite-rb-to-rb-alt
      page-dir-ptr-table-entry-addr-to-c-program-optimized-form
      unsigned-byte-p-52-of-left-shifting-a-40-bit-vector-by-12
      (:meta acl2::mv-nth-cons-meta)
      (:rewrite mv-nth-0-las-to-pas-subset-p)
      (:definition subset-p)
      (:rewrite mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs-alt)
      (:rewrite mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs)
      (:rewrite member-p-canonical-address-listp)
      (:rewrite mv-nth-0-las-to-pas-subset-p-with-l-addrs-from-bind-free)
      (:definition create-canonical-address-list)
      (:type-prescription member-p)
      (:rewrite two-mv-nth-1-las-to-pas-subset-p-disjoint-from-las-to-pas)
      (:rewrite open-mv-nth-1-las-to-pas-for-same-1g-page-general-1)
      (:rewrite r/x-is-irrelevant-for-mv-nth-2-las-to-pas-when-no-errors)
      (:rewrite mv-nth-2-las-to-pas-system-level-non-marking-mode)
      (:rewrite canonical-address-p-rip)
      (:rewrite xr-page-structure-marking-mode-mv-nth-2-las-to-pas)
      (:rewrite
       mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures)
      (:rewrite
       combine-mv-nth-2-las-to-pas-same-r-w-x-when-addresses-in-sequence)
      (:definition int-lists-in-seq-p)
      (:rewrite disjoint-p-two-addr-ranges-thm-3)
      (:rewrite disjoint-p-two-addr-ranges-thm-2)
      (:rewrite greater-logbitp-of-unsigned-byte-p . 2)
      (:rewrite subset-p-two-addr-ranges)
      (:rewrite xr-page-structure-marking-mode-mv-nth-1-wb)
      (:rewrite rm-low-64-in-programmer-level-mode)
      (:rewrite member-p-addr-range)
      (:type-prescription acl2::|x < y  =>  0 < y-x|)
      (:rewrite
       all-mem-except-paging-structures-equal-aux-and-rm-low-64-from-rest-of-memory)
      (:rewrite
       all-mem-except-paging-structures-equal-and-rm-low-64-from-rest-of-memory)
      (:type-prescription member-p-physical-address-p-physical-address-listp)
      (:linear n64p-rm-low-64)
      (:rewrite multiples-of-8-and-disjointness-of-physical-addresses-1)
      (:rewrite
       int-lists-in-seq-p-and-append-with-create-canonical-address-list-2)
      (:rewrite
       infer-disjointness-with-all-translation-governing-addresses-from-gather-all-paging-structure-qword-addresses-with-disjoint-p$)
      (:rewrite car-addr-range)
      (:type-prescription member-p-physical-address-p)
      (:type-prescription n01p-page-size)
      (:rewrite acl2::consp-of-append)
      (:rewrite disjoint-p-two-addr-ranges-thm-0)
      (:rewrite not-disjoint-p-two-addr-ranges-thm)
      (:rewrite right-shift-to-logtail)
      (:rewrite disjoint-p-two-addr-ranges-thm-1)
      (:type-prescription int-lists-in-seq-p)
      (:rewrite cdr-addr-range)
      (:type-prescription n01p-page-user-supervisor)
      (:type-prescription n01p-page-read-write)
      (:type-prescription n01p-page-present)
      (:type-prescription n01p-page-execute-disable)
      (:rewrite int-lists-in-seq-p-and-append)
      (:rewrite member-p-addr-range-from-member-p-addr-range)
      (:rewrite car-of-append)
      (:rewrite
       xlate-equiv-structures-and-logtail-30-rm-low-64-with-page-dir-ptr-table-entry-addr)
      (:type-prescription xlate-equiv-memory)
      (:rewrite open-mv-nth-0-las-to-pas-for-same-1g-page-general-2)
      (:rewrite loghead-30-of-1g-aligned-lin-addr-+-n-2)
      (:type-prescription rm-low-64-logand-logior-helper-1)
      (:rewrite
       canonical-address-p-pml4-table-entry-addr-to-c-program-optimized-form)
      (:rewrite xlate-equiv-structures-and-logtail-12-rm-low-64-with-pml4-table-entry-addr)
      (:rewrite unsigned-byte-p-of-combine-bytes-and-rb-in-system-level-mode)
      (:rewrite acl2::right-cancellation-for-+)
      (:rewrite pml4-table-entry-addr-is-a-multiple-of-8)
      (:rewrite ctri-is-n64p))))))

;; ======================================================================

;; Three top-level theorems:

;; 1. No errors encountered during program run; also, final state is
;; still in the system-level marking mode.

(defthmd no-errors-during-program-execution
  ;; Derived from ms-fault-programmer-level-and-marking-mode-from-final-state.
  (implies (rewire_dst_to_src-effects-preconditions x86)
	   (and (equal (xr :ms                          0 (x86-run (rewire_dst_to_src-clk) x86)) nil)
		(equal (xr :fault                       0 (x86-run (rewire_dst_to_src-clk) x86)) nil)
		(equal (xr :programmer-level-mode       0 (x86-run (rewire_dst_to_src-clk) x86)) nil)
		(equal (xr :page-structure-marking-mode 0 (x86-run (rewire_dst_to_src-clk) x86)) t)))
  :hints (("Goal"
	   :use ((:instance ms-fault-programmer-level-and-marking-mode-from-final-state))
	   :in-theory (theory 'minimal-theory))))

;; 2. Destination data in final state == source data in initial state,
;; i.e., copy was done successfully.

(defthm destination-data-in-final-state-==-source-data-in-initial-state
  (implies (and
	    (rewire_dst_to_src-effects-preconditions x86)
	    (source-data-preconditions x86)
	    (destination-data-preconditions x86))
	   (equal
	    ;; Destination, after the copy:
	    (mv-nth 1 (rb (create-canonical-address-list *2^30* (xr :rgf *rsi* x86))
			  :r (x86-run (rewire_dst_to_src-clk) x86)))
	    ;; Source, before the copy:
	    (mv-nth 1 (rb (create-canonical-address-list *2^30* (xr :rgf *rdi* x86))
			  :r x86))))
  :hints (("Goal"
	   :do-not '(preprocess)
	   :do-not-induct t
	   :hands-off (x86-run)
	   :use ((:instance destination-data-from-final-state-in-terms-of-read-from-physical-memory-and-addr-range)
		 (:instance source-data-from-initial-state-in-terms-of-read-from-physical-memory-and-addr-range)
		 (:instance throwaway-destination-data-preconditions-lemma))
	   :in-theory (union-theories
		       '()
		       (theory 'minimal-theory)))))

;; 3. Source data in the final state === source data in the initial
;; state, i.e., the source data is unmodified.

(defthm source-data-in-final-state-==-source-data-in-initial-state
  (implies (and (rewire_dst_to_src-effects-preconditions x86)
		(source-data-preconditions x86))

	   (equal
	    (mv-nth 1 (rb (create-canonical-address-list *2^30* (xr :rgf *rdi* x86))
			  :r
			  (x86-run (rewire_dst_to_src-clk) x86)))
	    (mv-nth 1 (rb (create-canonical-address-list *2^30* (xr :rgf *rdi* x86))
			  :r x86))))
  :hints (("Goal"
	   :use ((:instance source-data-from-final-state-in-terms-of-rb))
	   :in-theory (union-theories
		       '(source-data-preconditions)
		       (theory 'minimal-theory)))))


;; 4. Program unmodified in the final state:

(defthm program-at-alt-and-wb-to-paging-structures
  (implies
   (and
    (equal (page-size value) 1)
    (direct-map-p 8 lin-addr :w (cpl x86) (double-rewrite x86))
    (disjoint-p$
     (mv-nth 1 (las-to-pas l-addrs :x (cpl x86) (double-rewrite x86)))
     (open-qword-paddr-list
      (gather-all-paging-structure-qword-addresses (double-rewrite x86))))
    (disjoint-p$
     (mv-nth 1
	     (las-to-pas (create-canonical-address-list 8 lin-addr)
			 :w (cpl x86) (double-rewrite x86)))
     (all-translation-governing-addresses l-addrs (double-rewrite x86)))
    (disjoint-p$
     (mv-nth 1
	     (las-to-pas (create-canonical-address-list 8 lin-addr)
			 :w (cpl x86) (double-rewrite x86)))
     (mv-nth 1 (las-to-pas l-addrs :x (cpl x86) (double-rewrite x86))))
    (physical-address-p lin-addr)
    (equal (loghead 3 lin-addr) 0)
    (canonical-address-p lin-addr)
    (unsigned-byte-p 64 value)
    (x86p x86))
   (equal
    (program-at-alt
     l-addrs bytes
     (mv-nth 1
	     (wb (create-addr-bytes-alist (create-canonical-address-list 8 lin-addr)
					  (byte-ify 8 value))
		 x86)))
    (program-at-alt l-addrs bytes (double-rewrite x86))))
  :hints
  (("Goal"
    :do-not-induct t
    :use
    ((:instance disjointness-of-las-to-pas-from-wb-to-subset-of-paging-structures-general
		(l-addrs-subset l-addrs)
		(r-w-x :x)
		(cpl (cpl x86))
		(x86-1 x86)
		(x86-2 x86)))
    :in-theory (e/d* (program-at-alt program-at disjoint-p$ subset-p subset-p-reflexive program-at-alt)
		     (rewrite-program-at-to-program-at-alt)))))

(local
 (defthmd program-in-final-state-==-program-in-initial-state-helper
   (implies (rewire_dst_to_src-effects-preconditions x86)

	    (equal
	     (program-at-alt
	      (create-canonical-address-list *rewire_dst_to_src-len* (xr :rip 0 x86))
	      *rewire_dst_to_src*
	      ;; (x86-run (rewire_dst_to_src-clk) x86)
	      (xw
	       :rgf *rax* 1
	       (xw
		:rgf *rcx*
		(pml4-table-entry-addr (xr :rgf *rsi* x86) (pml4-table-base-addr x86))
		(xw
		 :rgf *rdx*
		 (logand
		  4503598553628672
		  (logior
		   (logand
		    -4503598553628673
		    (logext
		     64
		     (combine-bytes
		      (mv-nth
		       1
		       (rb
			(create-canonical-address-list
			 8
			 (page-dir-ptr-table-entry-addr
			  (xr :rgf *rsi* x86)
			  (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
			:r x86)))))
		   (logand
		    4503598553628672
		    (logext
		     64
		     (combine-bytes
		      (mv-nth
		       1
		       (rb
			(create-canonical-address-list
			 8
			 (page-dir-ptr-table-entry-addr
			  (xr :rgf *rdi* x86)
			  (pdpt-base-addr (xr :rgf *rdi* x86) x86)))
			:r x86)))))))
		 (xw
		  :rgf *rsp* (+ 8 (xr :rgf *rsp* x86))
		  (xw
		   :rgf *rsi* 0
		   (xw
		    :rgf *rdi*
		    (logand
		     4503598553628672
		     (logext
		      64
		      (combine-bytes
		       (mv-nth
			1
			(rb
			 (create-canonical-address-list
			  8
			  (page-dir-ptr-table-entry-addr
			   (xr :rgf *rdi* x86)
			   (pdpt-base-addr (xr :rgf *rdi* x86) x86)))
			 :r x86)))))
		    (xw
		     :rgf *r8* 1099511627775
		     (xw
		      :rgf *r9*
		      (logand
		       4503598553628672
		       (logext
			64
			(combine-bytes
			 (mv-nth
			  1
			  (rb
			   (create-canonical-address-list
			    8
			    (page-dir-ptr-table-entry-addr
			     (xr :rgf *rdi* x86)
			     (pdpt-base-addr (xr :rgf *rdi* x86) x86)))
			   :r x86)))))
		      (xw
		       :rip 0
		       (logext
			64
			(combine-bytes
			 (mv-nth 1
				 (rb (create-canonical-address-list 8 (xr :rgf *rsp* x86))
				     :r x86))))
		       (xw
			:undef 0 (+ 46 (nfix (xr :undef 0 x86)))
			(!flgi
			 *cf*
			 (bool->bit
			  (<
			   (logand
			    4503598553628672
			    (combine-bytes
			     (mv-nth
			      1
			      (rb
			       (create-canonical-address-list
				8
				(page-dir-ptr-table-entry-addr
				 (xr :rgf *rdi* x86)
				 (pdpt-base-addr (xr :rgf *rdi* x86) x86)))
			       :r x86))))
			   (logand
			    4503598553628672
			    (logior
			     (logand
			      18442240475155922943
			      (combine-bytes
			       (mv-nth
				1
				(rb
				 (create-canonical-address-list
				  8
				  (page-dir-ptr-table-entry-addr
				   (xr :rgf *rsi* x86)
				   (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
				 :r x86))))
			     (logand
			      4503598553628672
			      (combine-bytes
			       (mv-nth
				1
				(rb
				 (create-canonical-address-list
				  8
				  (page-dir-ptr-table-entry-addr
				   (xr :rgf *rdi* x86)
				   (pdpt-base-addr (xr :rgf *rdi* x86) x86)))
				 :r x86))))))))
			 (!flgi
			  *pf*
			  (pf-spec64
			   (loghead
			    64
			    (+
			     (logand
			      4503598553628672
			      (logext
			       64
			       (combine-bytes
				(mv-nth
				 1
				 (rb
				  (create-canonical-address-list
				   8
				   (page-dir-ptr-table-entry-addr
				    (xr :rgf *rdi* x86)
				    (pdpt-base-addr (xr :rgf *rdi* x86) x86)))
				  :r x86)))))
			     (-
			      (logand
			       4503598553628672
			       (logior
				(logand
				 -4503598553628673
				 (logext
				  64
				  (combine-bytes
				   (mv-nth
				    1
				    (rb
				     (create-canonical-address-list
				      8
				      (page-dir-ptr-table-entry-addr
				       (xr :rgf *rsi* x86)
				       (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
				     :r x86)))))
				(logand
				 4503598553628672
				 (logext
				  64
				  (combine-bytes
				   (mv-nth
				    1
				    (rb
				     (create-canonical-address-list
				      8
				      (page-dir-ptr-table-entry-addr
				       (xr :rgf *rdi* x86)
				       (pdpt-base-addr (xr :rgf *rdi* x86) x86)))
				     :r x86)))))))))))
			  (!flgi
			   *af*
			   (sub-af-spec64
			    (logand
			     4503598553628672
			     (combine-bytes
			      (mv-nth
			       1
			       (rb
				(create-canonical-address-list
				 8
				 (page-dir-ptr-table-entry-addr
				  (xr :rgf *rdi* x86)
				  (pdpt-base-addr (xr :rgf *rdi* x86) x86)))
				:r x86))))
			    (logand
			     4503598553628672
			     (logior
			      (logand
			       18442240475155922943
			       (combine-bytes
				(mv-nth
				 1
				 (rb
				  (create-canonical-address-list
				   8
				   (page-dir-ptr-table-entry-addr
				    (xr :rgf *rsi* x86)
				    (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
				  :r x86))))
			      (logand
			       4503598553628672
			       (combine-bytes
				(mv-nth
				 1
				 (rb
				  (create-canonical-address-list
				   8
				   (page-dir-ptr-table-entry-addr
				    (xr :rgf *rdi* x86)
				    (pdpt-base-addr (xr :rgf *rdi* x86) x86)))
				  :r x86)))))))
			   (!flgi
			    *zf* 1
			    (!flgi
			     *sf*
			     (sf-spec64
			      (loghead
			       64
			       (+
				(logand
				 4503598553628672
				 (logext
				  64
				  (combine-bytes
				   (mv-nth
				    1
				    (rb
				     (create-canonical-address-list
				      8
				      (page-dir-ptr-table-entry-addr
				       (xr :rgf *rdi* x86)
				       (pdpt-base-addr (xr :rgf *rdi* x86) x86)))
				     :r x86)))))
				(-
				 (logand
				  4503598553628672
				  (logior
				   (logand
				    -4503598553628673
				    (logext
				     64
				     (combine-bytes
				      (mv-nth
				       1
				       (rb
					(create-canonical-address-list
					 8
					 (page-dir-ptr-table-entry-addr
					  (xr :rgf *rsi* x86)
					  (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
					:r x86)))))
				   (logand
				    4503598553628672
				    (logext
				     64
				     (combine-bytes
				      (mv-nth
				       1
				       (rb
					(create-canonical-address-list
					 8
					 (page-dir-ptr-table-entry-addr
					  (xr :rgf *rdi* x86)
					  (pdpt-base-addr (xr :rgf *rdi* x86) x86)))
					:r x86)))))))))))
			     (!flgi
			      *of*
			      (of-spec64
			       (+
				(logand
				 4503598553628672
				 (logext
				  64
				  (combine-bytes
				   (mv-nth
				    1
				    (rb
				     (create-canonical-address-list
				      8
				      (page-dir-ptr-table-entry-addr
				       (xr :rgf *rdi* x86)
				       (pdpt-base-addr (xr :rgf *rdi* x86) x86)))
				     :r x86)))))
				(-
				 (logand
				  4503598553628672
				  (logior
				   (logand
				    -4503598553628673
				    (logext
				     64
				     (combine-bytes
				      (mv-nth
				       1
				       (rb
					(create-canonical-address-list
					 8
					 (page-dir-ptr-table-entry-addr
					  (xr :rgf *rsi* x86)
					  (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
					:r x86)))))
				   (logand
				    4503598553628672
				    (logext
				     64
				     (combine-bytes
				      (mv-nth
				       1
				       (rb
					(create-canonical-address-list
					 8
					 (page-dir-ptr-table-entry-addr
					  (xr :rgf *rdi* x86)
					  (pdpt-base-addr (xr :rgf *rdi* x86) x86)))
					:r x86))))))))))
			      (mv-nth
			       2
			       (las-to-pas
				(create-canonical-address-list 8 (xr :rgf *rsp* x86))
				:r 0
				(mv-nth
				 2
				 (las-to-pas
				  (create-canonical-address-list
				   40 (+ 206 (xr :rip 0 x86)))
				  :x 0
				  (mv-nth
				   2
				   (las-to-pas
				    (create-canonical-address-list
				     15 (+ 190 (xr :rip 0 x86)))
				    :x 0
				    (mv-nth
				     1
				     (wb
				      (create-addr-bytes-alist
				       (create-canonical-address-list
					8
					(page-dir-ptr-table-entry-addr
					 (xr :rgf *rsi* x86)
					 (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
				       (byte-ify
					8
					(logior
					 (logand
					  18442240475155922943
					  (combine-bytes
					   (mv-nth
					    1
					    (rb
					     (create-canonical-address-list
					      8
					      (page-dir-ptr-table-entry-addr
					       (xr :rgf *rsi* x86)
					       (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
					     :r x86))))
					 (logand
					  4503598553628672
					  (combine-bytes
					   (mv-nth
					    1
					    (rb
					     (create-canonical-address-list
					      8
					      (page-dir-ptr-table-entry-addr
					       (xr :rgf *rdi* x86)
					       (pdpt-base-addr (xr :rgf *rdi* x86) x86)))
					     :r x86)))))))
				      (mv-nth
				       2
				       (las-to-pas
					(create-canonical-address-list
					 6 (+ 184 (xr :rip 0 x86)))
					:x 0
					(mv-nth
					 2
					 (las-to-pas
					  (create-canonical-address-list
					   8
					   (page-dir-ptr-table-entry-addr
					    (xr :rgf *rsi* x86)
					    (pdpt-base-addr (xr :rgf *rsi* x86) x86)))
					  :r 0
					  (mv-nth
					   2
					   (las-to-pas
					    (create-canonical-address-list
					     40 (+ 144 (xr :rip 0 x86)))
					    :x 0
					    (mv-nth
					     2
					     (las-to-pas
					      (create-canonical-address-list
					       3 (+ 140 (xr :rip 0 x86)))
					      :x 0
					      (mv-nth
					       2
					       (las-to-pas
						(create-canonical-address-list
						 8
						 (pml4-table-entry-addr
						  (xr :rgf *rsi* x86)
						  (pml4-table-base-addr x86)))
						:r 0
						(mv-nth
						 2
						 (las-to-pas
						  (create-canonical-address-list
						   32 (+ 108 (xr :rip 0 x86)))
						  :x 0
						  (mv-nth
						   2
						   (las-to-pas
						    (create-canonical-address-list
						     18 (+ 86 (xr :rip 0 x86)))
						    :x 0
						    (mv-nth
						     2
						     (las-to-pas
						      (create-canonical-address-list
						       8
						       (page-dir-ptr-table-entry-addr
							(xr :rgf *rdi* x86)
							(pdpt-base-addr (xr :rgf *rdi* x86) x86)))
						      :r 0
						      (mv-nth
						       2
						       (las-to-pas
							(create-canonical-address-list
							 40 (+ 46 (xr :rip 0 x86)))
							:x 0
							(mv-nth
							 2
							 (las-to-pas
							  (create-canonical-address-list
							   4 (+ 38 (xr :rip 0 x86)))
							  :x 0
							  (mv-nth
							   2
							   (las-to-pas
							    (create-canonical-address-list
							     8
							     (pml4-table-entry-addr
							      (xr :rgf *rdi* x86)
							      (pml4-table-base-addr x86)))
							    :r 0
							    (mv-nth
							     2
							     (las-to-pas
							      (create-canonical-address-list
							       25 (+ 13 (xr :rip 0 x86)))
							      :x 0
							      (mv-nth
							       2
							       (las-to-pas
								(create-canonical-address-list
								 8
								 (+ -24 (xr :rgf *rsp* x86)))
								:r 0
								(mv-nth
								 2
								 (las-to-pas
								  (create-canonical-address-list
								   5 (+ 8 (xr :rip 0 x86)))
								  :x 0
								  (mv-nth
								   1
								   (wb
								    (create-addr-bytes-alist
								     (create-canonical-address-list
								      8
								      (+ -24 (xr :rgf *rsp* x86)))
								     (byte-ify
								      8
								      (xr :ctr *cr3* x86)))
								    (mv-nth
								     2
								     (las-to-pas
								      (create-canonical-address-list
								       8 (xr :rip 0 x86))
								      :x 0
								      x86)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
	     (program-at (create-canonical-address-list *rewire_dst_to_src-len* (xr :rip 0 x86))
			 *rewire_dst_to_src* x86)))
   :hints (("Goal"
	    :hands-off (x86-run)
	    :in-theory (e/d* (page-size)
			     ((:rewrite mv-nth-0-las-to-pas-subset-p)
			      (:definition subset-p)
			      (:definition member-p)
			      (:rewrite rewrite-rb-to-rb-alt)
			      (:rewrite mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs)
			      (:rewrite subset-p-two-create-canonical-address-lists-general)
			      (:rewrite member-p-canonical-address-listp)
			      (:rewrite page-dir-ptr-table-entry-addr-to-c-program-optimized-form)
			      (:rewrite len-of-rb-in-system-level-mode)
			      (:linear adding-7-to-page-dir-ptr-table-entry-addr)
			      (:rewrite acl2::loghead-identity)
			      (:rewrite mv-nth-0-las-to-pas-subset-p-with-l-addrs-from-bind-free)
			      (:linear *physical-address-size*p-page-dir-ptr-table-entry-addr)
			      (:rewrite cdr-mv-nth-1-las-to-pas)
			      (:rewrite
			       mv-nth-0-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p)
			      (:rewrite mv-nth-1-las-to-pas-subset-p-disjoint-from-other-p-addrs-alt)
			      (:rewrite disjoint-p-subset-p)
			      (:rewrite greater-logbitp-of-unsigned-byte-p . 2)
			      (:rewrite cdr-create-canonical-address-list)
			      (:rewrite unsigned-byte-p-of-combine-bytes)
			      (:definition create-canonical-address-list)
			      (:linear size-of-combine-bytes)
			      (:linear unsigned-byte-p-of-combine-bytes)
			      (:rewrite default-+-2)
			      (:rewrite two-mv-nth-1-las-to-pas-subset-p-disjoint-from-las-to-pas)
			      (:rewrite
			       infer-disjointness-with-all-translation-governing-addresses-from-gather-all-paging-structure-qword-addresses-with-disjoint-p$)
			      (:rewrite loghead-of-non-integerp)
			      (:type-prescription acl2::|x < y  =>  0 < -x+y|)
			      (:rewrite acl2::equal-of-booleans-rewrite)
			      (:linear rip-is-i48p . 2)
			      (:type-prescription member-p)
			      (:linear rip-is-i48p . 1)
			      (:linear rgfi-is-i64p . 2)
			      (:rewrite default-<-1)
			      (:rewrite default-+-1)
			      (:rewrite canonical-address-p-limits-thm-0)
			      (:linear rgfi-is-i64p . 1)
			      (:rewrite default-<-2)
			      (:rewrite bitops::unsigned-byte-p-when-unsigned-byte-p-less)
			      (:rewrite loghead-negative)
			      (:rewrite consp-of-create-canonical-address-list)
			      (:rewrite car-create-canonical-address-list)
			      (:type-prescription pdpt-base-addr)
			      (:rewrite canonical-address-p-limits-thm-3)
			      (:definition no-duplicates-p)
			      (:rewrite member-p-cdr)
			      (:rewrite consp-mv-nth-1-las-to-pas)
			      (:rewrite member-p-of-not-a-consp)
			      (:meta acl2::cancel_plus-equal-correct)
			      (:meta acl2::cancel_times-equal-correct)
			      (:rewrite subset-p-cdr-y)
			      (:meta acl2::cancel_plus-lessp-correct)
			      (:rewrite canonical-address-p-limits-thm-1)
			      (:rewrite member-p-of-subset-is-member-p-of-superset)
			      (:rewrite acl2::consp-when-member-equal-of-atom-listp)
			      (:rewrite rationalp-implies-acl2-numberp)
			      (:linear adding-7-to-pml4-table-entry-addr)
			      (:type-prescription adding-7-to-page-dir-ptr-table-entry-addr)
			      (:definition create-addr-bytes-alist)
			      (:rewrite member-p-and-mult-8-qword-paddr-listp)
			      (:rewrite mv-nth-1-las-to-pas-subset-p)
			      (:type-prescription booleanp)
			      (:rewrite default-car)
			      (:rewrite default-cdr)
			      (:definition combine-bytes)
			      (:linear ia32e-la-to-pa-<-*mem-size-in-bytes-15*-when-low-12-bits-=-4081)
			      (:linear ia32e-la-to-pa-<-*mem-size-in-bytes-1*-when-low-12-bits-=-4090)
			      (:linear ia32e-la-to-pa-<-*mem-size-in-bytes-1*-when-low-12-bits-=-4089)
			      (:rewrite acl2::ash-0)
			      (:linear *physical-address-size*p-pml4-table-entry-addr)
			      (:rewrite
			       mv-nth-1-ia32e-la-to-pa-member-of-mv-nth-1-las-to-pas-if-lin-addr-member-p)
			      (:rewrite acl2::zip-open)
			      (:rewrite acl2::equal-constant-+)
			      (:rewrite acl2::difference-unsigned-byte-p)
			      (:linear ia32e-la-to-pa-<-*mem-size-in-bytes-15*-when-low-12-bits-<-4081)
			      (:linear ia32e-la-to-pa-<-*mem-size-in-bytes-1*-when-low-12-bits-<-4093)
			      (:linear ia32e-la-to-pa-<-*mem-size-in-bytes-1*-when-low-12-bits-<-4089)
			      (:linear
			       ia32e-la-to-pa-<-*mem-size-in-bytes-1*-when-low-12-bits-!=-all-ones)
			      (:definition nthcdr)
			      (:definition nth)
			      (:type-prescription adding-7-to-pml4-table-entry-addr)
			      (:rewrite subset-p-cdr-x)
			      (:linear ash-monotone-2)
			      (:rewrite combine-mv-nth-2-las-to-pas-same-r-w-x-when-addresses-in-sequence)
			      (:rewrite create-canonical-address-list-1)
			      (:rewrite car-mv-nth-1-las-to-pas)
			      (:definition byte-listp)
			      (:definition int-lists-in-seq-p)
			      (:type-prescription bitops::logand-natp-type-2)
			      (:meta acl2::mv-nth-cons-meta)
			      (:linear bitops::upper-bound-of-logand . 2)
			      (:linear bitops::logand->=-0-linear-2)
			      (:definition binary-append)
			      (:rewrite xr-page-structure-marking-mode-mv-nth-2-las-to-pas)
			      (:rewrite consp-byte-ify)
			      (:linear n52p-mv-nth-1-ia32e-la-to-pa)
			      (:rewrite acl2::cdr-of-append-when-consp)
			      (:linear <=-logior)
			      (:type-prescription bitops::logior-natp-type)
			      (:definition open-qword-paddr-list)
			      (:rewrite ia32e-la-to-pa-in-programmer-level-mode)
			      (:rewrite bitops::basic-unsigned-byte-p-of-+)
			      (:type-prescription byte-ify)
			      (:type-prescription n52p-mv-nth-1-ia32e-la-to-pa)
			      (:linear acl2::logext-bounds)
			      (:type-prescription acl2::logext-type)
			      (:rewrite mv-nth-1-ia32e-la-to-pa-when-error)
			      (:rewrite acl2::append-when-not-consp)
			      (:type-prescription consp-mv-nth-1-las-to-pas)
			      (:rewrite acl2::member-of-cons)
			      (:rewrite acl2::logext-identity)
			      (:definition n08p$inline)
			      (:rewrite acl2::natp-when-integerp)
			      (:rewrite member-p-start-rip-of-create-canonical-address-list)
			      (:rewrite mv-nth-2-las-to-pas-system-level-non-marking-mode)
			      (:rewrite acl2::natp-rw)
			      (:rewrite r/x-is-irrelevant-for-mv-nth-2-las-to-pas-when-no-errors)
			      (:linear bitops::logand-<-0-linear)
			      (:rewrite mv-nth-1-las-to-pas-when-error)
			      (:rewrite acl2::ifix-when-not-integerp)
			      (:linear acl2::expt->-1)
			      (:rewrite acl2::logtail-identity)
			      (:type-prescription bitops::logand-natp-type-1)
			      (:definition len)
			      (:rewrite wb-not-consp-addr-lst)
			      (:linear bitops::logior->=-0-linear)
			      (:linear bitops::logior-<-0-linear-1)
			      (:definition addr-range)
			      (:linear member-p-pos-value)
			      (:linear member-p-pos-1-value)
			      (:linear acl2::index-of-<-len)
			      (:rewrite right-shift-to-logtail)
			      (:rewrite r-w-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-when-no-errors)
			      (:type-prescription signed-byte-p)
			      (:rewrite default-unary-minus)
			      (:rewrite canonical-address-p-rip)
			      (:type-prescription binary-logand)
			      (:type-prescription true-listp-addr-range)
			      (:type-prescription consp-addr-range)
			      (:rewrite acl2::car-of-append)
			      (:definition acons)
			      (:rewrite acl2::natp-when-gte-0)
			      (:linear bitops::logior-<-0-linear-2)
			      (:linear mv-nth-1-idiv-spec)
			      (:linear mv-nth-1-div-spec)
			      (:type-prescription acl2::|x < y  =>  0 < y-x|)
			      (:rewrite acl2::commutativity-2-of-+)
			      (:rewrite bitops::logbitp-nonzero-of-bit)
			      (:rewrite bitops::logand-with-negated-bitmask)
			      (:rewrite bitops::logand-with-bitmask)
			      (:rewrite xr-page-structure-marking-mode-mv-nth-1-wb)
			      (:rewrite
			       int-lists-in-seq-p-and-append-with-create-canonical-address-list-2)
			      (:type-prescription zip)
			      (:type-prescription rm-low-64-logand-logior-helper-1)
			      (:rewrite negative-logand-to-positive-logand-with-integerp-x)
			      (:rewrite weed-out-irrelevant-logand-when-first-operand-constant)
			      (:rewrite logand-redundant)
			      (:rewrite bitops::signed-byte-p-when-unsigned-byte-p-smaller)
			      (:rewrite bitops::signed-byte-p-when-signed-byte-p-smaller)
			      (:rewrite bitops::signed-byte-p-monotonicity)
			      (:rewrite acl2::consp-of-append)
			      (:type-prescription addr-byte-alistp-create-addr-bytes-alist)
			      (:type-prescription combine-bytes)
			      (:rewrite
			       mv-nth-1-rb-and-xlate-equiv-memory-disjoint-from-paging-structures)
			      (:rewrite car-addr-range)
			      (:linear bitops::upper-bound-of-logand . 1)
			      (:linear bitops::logand->=-0-linear-1)
			      (:rewrite acl2::commutativity-of-append-under-set-equiv)
			      (:rewrite consp-create-addr-bytes-alist)
			      (:type-prescription n64p$inline)
			      (:rewrite acl2::append-atom-under-list-equiv)
			      (:type-prescription gather-all-paging-structure-qword-addresses)
			      (:type-prescription binary-logior)
			      (:rewrite neg-addr-range=nil)
			      (:rewrite acl2::signed-byte-p-logops)
			      (:rewrite unsigned-byte-p-64-of-dest-pdpte-modified-value)
			      (:type-prescription acl2::bitmaskp$inline)
			      (:type-prescription consp-append)
			      (:rewrite acl2::subsetp-member . 2)
			      (:rewrite acl2::subsetp-member . 1)
			      (:linear combine-bytes-size-for-rm64-programmer-level-mode)
			      (:rewrite bitops::unsigned-byte-p-of-minus-when-signed-byte-p)
			      (:rewrite cdr-addr-range)
			      (:rewrite acl2::distributivity-of-minus-over-+)
			      (:type-prescription int-lists-in-seq-p)
			      (:type-prescription n01p-page-size)
			      (:rewrite bitops::logbitp-when-bitmaskp)
			      (:rewrite int-lists-in-seq-p-and-append)
			      (:type-prescription consp-create-addr-bytes-alist)
			      (:type-prescription bitp)
			      (:type-prescription all-translation-governing-addresses)
			      (:rewrite acl2::expt-with-violated-guards)
			      (:type-prescription consp-create-addr-bytes-alist-in-terms-of-len)
			      (:rewrite acl2::append-of-cons)
			      (:linear rm-low-64-logand-logior-helper-1)
			      (:type-prescription open-qword-paddr-list)
			      (:type-prescription acl2::true-listp-append)
			      (:type-prescription binary-append)
			      (:rewrite bitops::normalize-logbitp-when-mods-equal)
			      (:rewrite bitops::logbitp-of-negative-const)
			      (:rewrite bitops::logbitp-of-mask)
			      (:rewrite bitops::logbitp-of-const)
			      (:meta bitops::open-logbitp-of-const-lite-meta)
			      (:type-prescription natp)
			      (:type-prescription member-equal)
			      (:rewrite greater-logbitp-of-unsigned-byte-p . 1)
			      (:linear acl2::expt-is-increasing-for-base>1)
			      (:definition member-equal)
			      (:definition n64p$inline)
			      (:type-prescription true-listp-create-addr-bytes-alist)
			      (:rewrite no-duplicates-p-and-append)
			      (:rewrite inverse-of-+)
			      (:linear bitops::expt-2-lower-bound-by-logbitp)
			      (:linear ctri-is-n64p)
			      (:rewrite subset-p-cons-member-p-lemma)
			      (:rewrite not-member-p-when-disjoint-p)
			      (:rewrite constant-upper-bound-of-logior-for-naturals)
			      (:linear bitops::upper-bound-of-logior-for-naturals)
			      (:type-prescription member-p-physical-address-p-physical-address-listp)
			      (:type-prescription member-p-physical-address-p)
			      (:rewrite bitops::signed-byte-p-of-logext)
			      (:rewrite acl2::signed-byte-p-logext)
			      (:rewrite car-cons)))))))

(defthm program-at-alt-in-final-state-==-program-at-in-initial-state
  (implies (rewire_dst_to_src-effects-preconditions x86)
	   (equal
	    (program-at-alt
	     (create-canonical-address-list *rewire_dst_to_src-len* (xr :rip 0 x86))
	     *rewire_dst_to_src*
	     (x86-run (rewire_dst_to_src-clk) x86))
	    (program-at (create-canonical-address-list *rewire_dst_to_src-len* (xr :rip 0 x86))
			*rewire_dst_to_src* x86)))
  :hints (("Goal"
	   :hands-off (x86-run)
	   :in-theory (e/d* (program-in-final-state-==-program-in-initial-state-helper)
			    (rewire_dst_to_src-effects-preconditions))
	   :use ((:instance rewire_dst_to_src-effects)
		 (:instance program-in-final-state-==-program-in-initial-state-helper)))))

(defthmd cpl-in-final-state
  (implies (rewire_dst_to_src-effects-preconditions x86)
	   (equal
	    (xr :seg-visible 1 (x86-run (rewire_dst_to_src-clk) x86))
	    (xr :seg-visible 1 x86)))
  :hints (("Goal"
	   :do-not '(preprocess)
	   :use ((:instance rewire_dst_to_src-effects)
		 (:instance fault-from-final-state))
	   :hands-off (x86-run)
	   :in-theory (e/d*
		       (rewire_dst_to_src-effects-preconditions-and-ms-fault-programmer-level-and-marking-mode-fields)
		       (rewire_dst_to_src-effects-preconditions)))))

(local
 (defthmd program-at-alt-in-final-state-==-program-at-in-final-state
   (implies (rewire_dst_to_src-effects-preconditions x86)
	    (equal
	     (program-at-alt
	      (create-canonical-address-list *rewire_dst_to_src-len* (xr :rip 0 x86))
	      *rewire_dst_to_src*
	      (x86-run (rewire_dst_to_src-clk) x86))
	     (program-at
	      (create-canonical-address-list *rewire_dst_to_src-len* (xr :rip 0 x86))
	      *rewire_dst_to_src*
	      (x86-run (rewire_dst_to_src-clk) x86))))
   :hints (("Goal"
	    :hands-off (x86-run)
	    :use ((:instance no-errors-during-program-execution)
		  (:instance program-at-alt-in-final-state-==-program-at-in-final-state-helper-1)
		  (:instance program-at-alt-in-final-state-==-program-at-in-final-state-helper-3))
	    :in-theory (e/d* (cpl-in-final-state
			      program-at-alt
			      disjoint-p$)
			     (rewrite-program-at-to-program-at-alt
			      rewire_dst_to_src-effects-preconditions))))))


(defthm program-in-final-state-==-program-in-initial-state
  (implies (rewire_dst_to_src-effects-preconditions x86)
	   (equal
	    (program-at
	     (create-canonical-address-list *rewire_dst_to_src-len* (xr :rip 0 x86))
	     *rewire_dst_to_src*
	     (x86-run (rewire_dst_to_src-clk) x86))
	    (program-at (create-canonical-address-list *rewire_dst_to_src-len* (xr :rip 0 x86))
			*rewire_dst_to_src* x86)))
  :hints (("Goal"
	   :hands-off (x86-run)
	   :in-theory (e/d* ()
			    (rewire_dst_to_src-effects-preconditions
			     force (force)))
	   :use ((:instance program-at-alt-in-final-state-==-program-at-in-initial-state)
		 (:instance program-at-alt-in-final-state-==-program-at-in-final-state)))))

;; !! TODO: How much stack was used?

;; ======================================================================
