;  Copyright (C) 2000 Panagiotis Manolios

;  This program is free software; you can redistribute it and/or modify
;  it under the terms of the GNU General Public License as published by
;  the Free Software Foundation; either version 2 of the License, or
;  (at your option) any later version.

;  This program is distributed in the hope that it will be useful,
;  but WITHOUT ANY WARRANTY; without even the implied warranty of
;  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;  GNU General Public License for more details.

;  You should have received a copy of the GNU General Public License
;  along with this program; if not, write to the Free Software
;  Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

;  Written by Panagiotis Manolios who can be reached as follows.

;  Email: pete@cs.utexas.edu

;  Postal Mail:
;  Department of Computer Science
;  The University of Texas at Austin
;  Austin, TX 78701 USA

(in-package "ACL2")
(include-book "../serial/serial")
(include-book "../../../top/alist-thms")

; This function generates a netlist for a ripple-carry adder.

(defun adder-net (plist qlist c i)
  (cond
   ((endp plist)
    `((,i ,c *)))
   (t `((,i (b--xor ,(car qlist) ,c))
        (,(+ i 1) (b--xor ,(car plist) ,i) *)
        (,(+ i 2) (b--maj ,(car plist) ,(car qlist) ,c))
        ,@(adder-net (cdr plist)
                     (cdr qlist)
                     (+ i 2)
                     (+ i 3))))))

#|
For example:

(adder-net '(a0 a1 a2) '(b0 b1 b2) 'c 0)

A two-bit adder

(defconst *2a* '(a0 a1))
(defconst *2b* '(b0 b1))
(defconst *2bit* (adder-net *2a* *2b* 'c 0))
|#

; Here is the semantics of this simple netlist description language.

(defun vals (names alist)
  (cond ((endp names) nil)
        (t (cons (value-of (car names) alist)
                 (vals (cdr names) alist)))))

(defun gate-val (gate alist)
  (cond
   ((atom gate) (value-of gate alist))
   (t (case (car gate)
	(b--xor (b--xor (value-of (cadr gate) alist)
		      (value-of (caddr gate) alist)))
	(b--maj (b--maj (value-of (cadr gate) alist)
		      (value-of (caddr gate) alist)
		      (value-of (cadddr gate) alist)))
	(t nil)))))

(defun net-val (netlist alist)
  (cond
   ((endp netlist) nil)
   (t (let ((val (gate-val (cadr (car netlist)) alist)))
        (cond
         ((eq (caddr (car netlist)) '*)
          (cons val
                (net-val (cdr netlist)
                         (cons (cons (car (car netlist))
                                     val)
                               alist))))
         (t (net-val (cdr netlist)
                     (cons (cons (car (car netlist))
                                 val)
                           alist))))))))

#|
For example,

(net-val '((0 (b--xor b c))
           (1 (b--xor a 0) *))
         '((a . t) (b . nil) (c . nil)))

1 + 2
(net-val *2bit* '((a0 . t) (b1 . t)))

2 + 2
(net-val *2bit* '((a1 . t) (b1 . t)))
|#

; Here are a few lemmas I will need.
(local
 (progn
   (defun hint (plist qlist c i alist)
     (cond ((endp plist) (list qlist c i alist))
	   (t (hint (cdr plist)
		    (cdr qlist)
		    (+ i 2)
		    (+ i 3)
		    (list* (cons (+ 2 i)
				 (b--maj (value-of (car plist) alist)
					 (value-of (car qlist) alist)
					 (value-of c alist)))
			   (cons (+ 1 i)
				 (b--xor (value-of (car plist) alist)
					 (b--xor (value-of (car qlist) alist)
						 (value-of c alist))))
			   (cons i
				 (b--xor (value-of (car qlist) alist)
					 (value-of c alist)))
			   alist)))))

   (defthm append-right-id
     (implies (true-listp a)
	      (equal (append a nil) a)))

   (defthm true-listp-adder-net
     (true-listp (adder-net plist qlist c i)))

   (defthm input-vals-not-changed
     (implies (and (integerp i)
		   (symbol-listp plist))
	      (equal (vals plist (cons (cons i x) alist))
		     (vals plist alist))))

   (defthm equal-len-0
     (equal (equal (len x) 0) (atom x)))
   ))

; This theorem establishes that the adder-net is correct, in the
; sense that its value is that of the serial adder.

(defthm adder-net-is-serial-adder
  (implies (and (symbol-listp plist)
		(symbol-listp qlist)
		(equal (len plist) (len qlist))
		(or (symbolp c)
		    (and (integerp c)
			 (< c i)))
		(integerp i))
	   (equal (net-val (adder-net plist qlist c i) alist)
		  (serial-adder (vals plist alist)
				(vals qlist alist)
				(value-of c alist))))
  :hints (("Goal" :induct (hint plist qlist c i alist)
	   :in-theory (disable b--xor b--maj))))

#|

We have, (but don't use):

(defthm adder-net-is-correct
  (implies (and (symbol-listp plist)
                (symbol-listp qlist)
                (equal (len plist) (len qlist))
                (or (symbolp c)
                    (and (integerp c)
                         (< c i)))
                (integerp i))
           (equal (n (net-val (adder-net plist qlist c i) alist))
                  (+ (n (vals plist alist))
                     (n (vals qlist alist))
                     (if (value-of c alist) 1 0)))))

|#

; Here is our 128 bit adder

(defconst *a*
  '(a00 a01 a02 a03 a04 a05 a06 a07 a08 a09
    a10 a11 a12 a13 a14 a15 a16 a17 a18 a19
    a20 a21 a22 a23 a24 a25 a26 a27 a28 a29
    a30 a31 a32 a33 a34 a35 a36 a37 a38 a39
    a40 a41 a42 a43 a44 a45 a46 a47 a48 a49
    a50 a51 a52 a53 a54 a55 a56 a57 a58 a59
    a60 a61 a62 a63 a64 a65 a66 a67 a68 a69
    a70 a71 a72 a73 a74 a75 a76 a77 a78 a79
    a80 a81 a82 a83 a84 a85 a86 a87 a88 a89
    a90 a91 a92 a93 a94 a95 a96 a97 a98 a99
    a100 a101 a102 a103 a104 a105 a106 a107
    a108 a109 a110 a111 a112 a113 a114 a115
    a116 a117 a118 a119 a120 a121 a122 a123
    a124 a125 a126 a127))

(defconst *b*
  '(b00 b01 b02 b03 b04 b05 b06 b07 b08 b09
    b10 b11 b12 b13 b14 b15 b16 b17 b18 b19
    b20 b21 b22 b23 b24 b25 b26 b27 b28 b29
    b30 b31 b32 b33 b34 b35 b36 b37 b38 b39
    b40 b41 b42 b43 b44 b45 b46 b47 b48 b49
    b50 b51 b52 b53 b54 b55 b56 b57 b58 b59
    b60 b61 b62 b63 b64 b65 b66 b67 b68 b69
    b70 b71 b72 b73 b74 b75 b76 b77 b78 b79
    b80 b81 b82 b83 b84 b85 b86 b87 b88 b89
    b90 b91 b92 b93 b94 b95 b96 b97 b98 b99
    b100 b101 b102 b103 b104 b105 b106 b107
    b108 b109 b110 b111 b112 b113 b114 b115
    b116 b117 b118 b119 b120 b121 b122 b123
    b124 b125 b126 b127))

(defconst *adder-128*
  (adder-net *a* *b* 'c 0))

#|

A 2-bit adder

(defconst *adder-2*
  (adder-net *2a* *2b* 'c 0))

|#

(local
(defthm serial-adder-adder-128
  (equal (net-val *adder-128* alist)
         (serial-adder (vals *a* alist)
		       (vals *b* alist)
		       (value-of 'c alist)))
  :hints (("Goal" :in-theory (disable net-val vals)
                  :use (:instance
                        adder-net-is-serial-adder
                        (plist *a*)
                        (qlist *b*)
                        (c 'c)
                        (i 0)))))
)

(defun bind (vars vals)
  (if (consp vars)
      (if (consp vals)
	  (acons (car vars) (car vals) (bind (cdr vars) (cdr vals)))
	(acons (car vars) nil (bind (cdr vars) nil)))
    nil))


(local
 (progn
   (defthm member-bind
     (implies (not (member x l))
	      (equal (vals l (cons (cons x y)
				   (bind l z)))
		     (vals l (bind l z)))))

   (defthm vals-bind-thm
     (implies (and (no-duplicatesp a)
		   (true-listp v1)
		   (equal (len a) (len v1)))
	      (equal (vals a (bind a v1))
		     v1)))

   (defun subset (x y)
     (if (consp x)
	 (and (member (car x) y)
	      (subset (cdr x) y))
       t))

   (in-theory (enable value-of))

   (defthm mem-bind
     (implies (member y x)
	      (equal (value-of y (append (bind x v1) z))
		     (value-of y (bind x v1)))))

   (defthm subset-bind
     (implies (subset a x)
	      (equal (vals a (append (bind x v1) z))
		     (vals a (bind x v1)))))

   (defthm subset-cons
     (implies (subset a b)
	      (subset a (cons c b))))

   (defthm subset-reflexive
     (subset a a))

   (defun disjoint (x y)
     (if (consp x)
	 (and (not (member (car x) y))
	      (disjoint (cdr x) y))
       t))

   (defthm not-mem-bind
     (implies (not (member y x))
	      (equal (value-of y (append (bind x v1) z))
		     (value-of y z))))

   (defthm disjoint-bind
     (implies (disjoint a x)
	      (equal (vals a (append (bind x v1) z))
		     (vals a z))))

   (defthm disjoint-comm
     (equal (disjoint b a)
	    (disjoint a b)))

   (defthm mem-val-bind
     (implies (not (member x a))
	      (equal (value-of x (bind a v1))
		     nil)))

   (in-theory (disable value-of))
   ))

(defun add (v1 v2)
  (let ((alist (append (bind *a* v1) (bind *b* v2))))
    (net-val *adder-128* alist)))

(local
 (defthm adder-net-is-serial-adder-2
   (implies (and (equal (len a) (len v1))
		 (equal (len b) (len v2))
		 (true-listp v1)
		 (true-listp v2)
		 (symbol-listp a)
		 (symbol-listp b)
		 (equal (len a) (len b))
		 (no-duplicatesp a)
		 (no-duplicatesp b)
		 (integerp i)
		 (symbolp c)
		 (not (member c a))
		 (not (member c b))
		 (disjoint a b))
	    (let ((alist (append (bind a v1) (bind b v2))))
	      (equal (net-val (adder-net a b c i) alist)
		     (serial-adder v1 v2 nil))))
   :hints (("Goal" :in-theory (disable b--xor b--maj adder-net-is-serial-adder serial-adder)
	    :use ((:instance
		   adder-net-is-serial-adder
		   (plist a)
		   (qlist b)
		   (alist (append (bind a v1) (bind b v2)))))
	    :do-not-induct t)))
 )

(defthm add-is-serial-adder
  (implies (and (equal (len *a*) (len v1))
		(equal (len *b*) (len v2))
		(true-listp v1)
		(true-listp v2))
	   (equal (add v1 v2)
		  (serial-adder v1 v2 nil)))
  :hints (("Goal" :in-theory (disable b--xor b--maj serial-adder bind serial-adder-adder-128)
                  :use (:instance
                        adder-net-is-serial-adder-2
			(a *a*) (b *b*) (i 0) (c 'c)))))

(defun net-ALU (op v1 v2)
  (cond ((equal op 0)
	 (128fix (add (128fix v1) (128fix v2))))
	(t (128fix (multiplier v1 v2 nil)))))

(local
 (defthm len-add-fix
   (implies (natp i)
	    (equal (len (add-fix i x))
		   i)))
 )

(defthm net-ALU-ALU-output
  (equal (net-ALU op v1 v2)
	 (serial-ALU op v1 v2)))

(defun net-excp (op v1 v2)
  (cond ((equal op 0)
	 (not (equal (n (128fix (add (128fix v1) (128fix v2))))
		     (n (serial-adder v1 v2 nil)))))
	(t (not (equal (n (128fix (multiplier v1 v2 nil)))
		       (n (multiplier v1 v2 nil)))))))

(defthm net-excp-serial-excp
  (equal (net-excp op v1 v2)
	 (serial-excp op v1 v2))
  :hints (("goal" :in-theory (disable serial-excp-excp))))
