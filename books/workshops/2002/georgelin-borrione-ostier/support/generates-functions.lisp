
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; This file generates functions for a formalization in ACL2
;                                                                          ;
;   Author : Philippe Georgelin                                            ;
;   Email : Philippe.Georgelin@st.com
;                                                                          ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "utils")

(defun make-namep (x)
  (make-name "" x "p"))


;; indentification of type
(defconst *int* 0)
(defconst *nat* 0)
(defconst *bit* 1)
(defconst *signed* 2)
(defconst *unsigned* 3)
(defconst *bit_vector* 3)

;; identification of functions
(defconst *error* 0)
(defconst *and* 1)
(defconst *or* 2)
(defconst *not* 3)
(defconst *xor* 4)
(defconst *nor* 5)
(defconst *nand* 6)

(defconst *+* 7)
(defconst *x* 8)
(defconst *-* 9)
(defconst *=* 10)
(defconst *others* 11)
(defconst *<=* 12)
(defconst *>=* 13)
(defconst *<* 14)
(defconst *>* 15)

(defconst *bits* 16)
(defconst *bitn* 17)
(defconst *round* 18)

;; array of true functions
(defconst *true_function*
  '((error error error error error)
    (logand b-and logand logand vec-and)
    (logior b-ior logior logior vec-or)
    (lognot b-not lognot lognot vec-not)
    (logxor b-xor logxor logxor vec-xor)
    (lognor b-nor lognor lognor vec-nor)
    (lognand b-nand lognand lognand vec-nand)
    (+ "non-defined_plus_on_bits" + + "non-defined_plus_on_bitvec")
    (* "non-defined_mult_on_bits" * * "non-defined_mult_on_bitvec")
    (- "non-defined_minus_on_bits" - - "non-defined_minus_on_bitvec")
    (= equal = = equal)
    (others others "non-defined_others_on_bits" others others
	    "non-defined_others_on_bit_vector")
    (<= <= "non_defined_<=-on-bits" <= <= "non_defined_<=-on-bitsvec")
    (>= >= "non_defined_>=-on-bits" >= >= "non_defined_<=-on-bitsvec")
    (< < "non_defined_<-on-bits" < < "non_defined_<=-on-bitsvec")
    (> > "non_defined_>-on-bits" > > "non_defined_<=-on-bitsvec")
    (bits bits bits bits bits bits)
    (bitn bitn bitn bitn bitn bitn)
    (round round round round round round)))


;; to change name of function by his constant
(defun change-to-const (name_func_or_type)
  (let ((name (if (consp name_func_or_type)
		  (car name_func_or_type)
		 name_func_or_type)))

   (case name
           ('and *and*)
           ('or *or*)
           ('not *not*)
           ('xor *xor*)
           ('nor *nor*)
           ('nand *nand*)
	   ('+ *+*)
	   ('- *-*)
	   ('* *x*)
	   ('= *=*)
	   ('equal *=*)
	   ('<= *<=*)
	   ('>= *>=*)
	   ('< *<*)
	   ('> *>*)

	   ('bits *bits*)
	   ('bitn *bitn*)
	   ('round *round*)

           ('integer *int*)
	   ('natural *int*)
           ('bit *bit*)
           ('signed *signed*)
           ('unsigned *unsigned*)
           ('bit_vector *bit_vector*)

	   ('others *others*)

           (otherwise name))))



(defun make-list-predicate (name-ent name-arch list_of_mem_elmts list_of_types)
  (if (endp list_of_mem_elmts)
    nil
    (if (consp (car list_of_types))
	(let* ((type (car list_of_types))
	       (kind (car type))
	       (size (caddr type))
	       (type_elmts (caddr type)))

	  (case kind
	      ('array
	       `( (true-listp
		   (,(make-name name-ent
				  name-arch
				  "-getst")
		    (quote ,(car list_of_mem_elmts))
		    st)
		  )
		  ( ,(make-name "array-" type_elmts "p")
		     (,(make-name name-ent
				  name-arch
				  "-getst")
		      (quote ,(car list_of_mem_elmts)) st)
		  )
		  (equal (length (,(make-name name-ent
					      name-arch
					      "-getst")
				  (quote ,(car list_of_mem_elmts))
				  st))
				 ,size)

		   ,@(make-list-predicate
		      name-ent
		      name-arch
		      (cdr list_of_mem_elmts)
		      (cdr list_of_types)))
	       )
	      ('std_logic_vector
	       `( (true-listp
		   (,(make-name name-ent
				  name-arch
				  "-getst")
		    (quote ,(car list_of_mem_elmts))
		    st)
		  )
		  ( ,(make-name "array-" "bit" "p")
		     (,(make-name name-ent
				  name-arch
				  "-getst")
		      (quote ,(car list_of_mem_elmts)) st)
		  )
		  (equal (length (,(make-name name-ent
					      name-arch
					      "-getst")
				  (quote ,(car list_of_mem_elmts))
				  st))
				 ,size)

		   ,@(make-list-predicate
		      name-ent
		      name-arch
		      (cdr list_of_mem_elmts)
		      (cdr list_of_types))))

	      ('bit_vector
	       `( (true-listp
		   (,(make-name name-ent
				  name-arch
				  "-getst")
		    (quote ,(car list_of_mem_elmts))
		    st)
		  )
		  ( ,(make-name "array-" "bit" "p")
		     (,(make-name name-ent
				  name-arch
				  "-getst")
		      (quote ,(car list_of_mem_elmts)) st)
		  )
		  (equal (length (,(make-name name-ent
					      name-arch
					      "-getst")
				  (quote ,(car list_of_mem_elmts))
				  st))
				 ,size)

		   ,@(make-list-predicate
		      name-ent
		      name-arch
		      (cdr list_of_mem_elmts)
		      (cdr list_of_types))))
))



       `( ( ,(make-namep (car list_of_types))
	      (,(make-name name-ent
			   name-arch
			   "-getst")
	       (quote ,(car list_of_mem_elmts)) st)
	   )
	   ,@(make-list-predicate
	      name-ent
	      name-arch
	      (cdr list_of_mem_elmts)
	      (cdr list_of_types))))))



(defun make-state-p (name-ent name_architecture
		     list_of_mem_elmts
		     list_of_types
		     channel state)
  (declare (xargs :stobjs state
		 :mode :program))

(fms "~%
(defun ~x0 (st)
 (declare (xargs :guard t))
      ~x1)~%"
(list
(cons #\0 (make-name name-ent name_architecture
	      "-stp"))
(cons #\1 (cons `and (append
		      (list '(true-listp st))
		      (list `(= (length st)
			       ,(length list_of_mem_elmts)))
		(make-list-predicate
		 name-ent
		 name_architecture
		 list_of_mem_elmts
		 list_of_types)))))
channel
state
nil))

; ---------- generating accessor getst and updater putst ------------

(defun make-next (list)
; This function generates a new list with next-name of values
  (if (endp list)
      nil
    (cons (make-name "" (car list) "+")
	  (make-next (cdr list))))
)

(defun make-list_of_component (list_of_configurations)
  (if (endp list_of_configurations)
      nil
    (let* ((comp_conf (car list_of_configurations))
	   (name-instance (car comp_conf)))
    (cons (make-name "" name-instance "")
	  (make-list_of_component (cdr list_of_configurations))))))


(defun make-getst-putst (name-ent name_arch
			 list_of_inputs
			 list_of_locals_signals
			 list_of_variables
			 list_of_outputs
			 list_of_configurations
			 channel
			 state)
(declare (xargs :stobjs state
		:mode :program))

(let ((total_list (append list_of_inputs
			  list_of_locals_signals
			  (make-next list_of_locals_signals)
			  list_of_variables
			  list_of_outputs
			  (make-next list_of_outputs)
			  (make-list_of_component list_of_configurations))))

(fms "
;; Accessor of the memory state : (getst var st) -> value~%
(defun ~x0 (var st)
  (declare (xargs :guard t)
	   (type ~x4 var)
           (type (satisfies true-listp) st))
  (nth (~x1 var) st))~%~%
;; Updater of the memory state : (putst ver new st) -> st~%
(defun ~x2 (var new st)
  (declare (xargs :guard t)
	   (type ~x4 var)
           (type (satisfies true-listp) st))
  (update-nth (~x1 var) new st))~%~%
;;;;;;;;;;;;;;"

(list
(cons #\0 (make-name name-ent name_arch "-getst"))
(cons #\1 (make-name name-ent name_arch "-get-nth"))
(cons #\2 (make-name name-ent name_arch "-putst"))
(cons #\3 (make-name name-ent name_arch "-stp"))
(cons #\4 (append (list 'member) total_list))
)

channel
state
nil)))



; -------------- generating function get-nth ----------------


(defun make-elmts-of-get-nth (list number)
  (if (endp list)
      nil
    `(((quote ,(car list))
		,number)
	  ,@(make-elmts-of-get-nth (cdr list)
				 (1+ number)))))



(defun make-get-nth (name-ent name_architecture
		     list_of_inputs
		     list_of_locals_signals
		     list_of_variables
		     list_of_outputs
		     list_of_configurations
		     channel state)
  (declare (xargs :stobjs state
		 :mode :program))
  (let ((number_of_elemts (+ (length list_of_inputs)
			    (length list_of_locals_signals)
			    (length (make-next
				     list_of_locals_signals))
			    (length list_of_variables)
			    (length list_of_configurations)
			    (length list_of_outputs)
			    (length (make-next
				       list_of_outputs))))
	(total_list (append list_of_inputs
			    list_of_locals_signals
			    (make-next list_of_locals_signals)
			    list_of_variables
			    list_of_outputs
			    (make-next list_of_outputs)
			    (make-list_of_component list_of_configurations))))

(fms "~%
;;; Function get-nth : gives the position of an element
;;; in the memory state ~%
(defun ~x0 (var)
   (declare (type ~x1 var)
	    (xargs :guard t))
   (the (integer 0 ~x2)
      ~x3))~%"

(list
(cons #\0 (make-name name-ent name_architecture
	      "-get-nth"))
(cons #\1 (append (list 'member) total_list))
(cons #\2 (1- number_of_elemts))
(cons #\3 (append (list 'case 'var)
		  (make-elmts-of-get-nth total_list 0))))
channel
state
nil)))


; ------------- generating macro make-state -----------------

(defun make-state-key-arg (list_of_mem_elmts list_of_types)
  (if (endp list_of_mem_elmts)
      nil
    (case (car list_of_types)
	  (positive
	   `( ( ,(car list_of_mem_elmts)
		'1
		)
	      ,@(make-state-key-arg (cdr list_of_mem_elmts)
				    (cdr list_of_types))))
	   (otherwise
	    `( ( ,(car list_of_mem_elmts)
		'0
		)
	      ,@(make-state-key-arg (cdr list_of_mem_elmts)
				    (cdr list_of_types)))))))


(defun make-state-key-arg2 (par_gen default_value)
  (if (endp par_gen)
      nil
    `( (,(car par_gen)
	(quote ,(car default_value))
       )
       ,@(make-state-key-arg2 (cdr par_gen)
			      (cdr default_value)))))

; (defun make-state-body (list_of_mem_elmts
; 			list_of_types)
;   (if (endp list_of_mem_elmts)
;       nil
;    ; (if (consp (car list_of_types))
;    ;	`( (defarray ,(nth 2 (car list_of_types))
; ;	             :initial-element
; ;		     ,(car list_of_mem_elmts)
; ;	   )
; ;	   ,@(make-state-body (cdr list_of_mem_elmts)
; ;			      (cdr list_of_types)))

;       `( ,(car list_of_mem_elmts)
; 	 ,@(make-state-body (cdr list_of_mem_elmts)
; 			      (cdr list_of_types)))))



(defun make-state-body-for-components (list_of_configurations)
  (if (endp list_of_configurations)
      nil
    (let* ((comp_conf (car list_of_configurations))
	   (name-ent (caddr comp_conf))
	   (name-arch (cadddr comp_conf)))
    `( (,(make-name name-ent name-arch "-make-state")
       )
       ,@(make-state-body-for-components
	  (cdr list_of_configurations))))))



(defun make-make-state (name-ent name_architecture
			list_of_mem_elmts
			list_of_types
			list_of_gener_param
			list_of_default_gene_para
			list_of_configurations
			 channel state)
  (declare (xargs :stobjs state
		 :mode :program))

(fms "~%
;;;;;;;  This macro make-state creates an initial state ;;;;;~%
(defun ~x0 () (let ~x1
  ~x2))"

(list (cons #\0 (make-name name-ent
			   name_architecture
			   "-make-state"))
      (cons #\1 (append (make-state-key-arg2 list_of_gener_param
					     list_of_default_gene_para)
			(make-state-key-arg list_of_mem_elmts list_of_types)
		        ))
      (cons #\2 (append (list 'list)
			(append list_of_gener_param
				list_of_mem_elmts
				)
			(make-state-body-for-components
			 list_of_configurations))))
channel
state
nil))


(defun make-update-state (name-ent name_architecture
			  channel state)
  (declare (xargs :stobjs state
		 :mode :program))

(fms "~%
;;;;;  This function updates memory state ;;;;~%
(defun ~x0 (key-arg st)
  (update-state-body ~x1 ~x2 key-arg st))"

(list
 (cons #\0 (make-name name-ent
		      name_architecture
		      "-update-st"))
 (cons #\1 (string name-ent))
 (cons #\2 (string name_architecture)))

channel
state
nil))



(defun make_name_var_sig (name bool)
  (if bool
      (make-name "" name "+")
    name))


(defun slice-rec2 (name-ent name_arch
		   name_var1
		   signed
		   max1
		   int1
		   int2
		   bool_sig_var)
  (declare (xargs :measure (nfix (- max1 int1))))
  (if (and (integerp max1) (integerp int1) (>= (- max1 int1) 0)
	   (integerp int2))
      (if (= (nfix (- max1 int1)) 0)

	  `((,(make-name name-ent name_arch "-putst")
	      (quote ,(make_name_var_sig name_var1
					 bool_sig_var))
	        (setarrayi ,int1
		          (logbit ,int2 ,signed)
				  (,(make-name name-ent
					       name_arch
					       "-getst")
				    (quote ,name_var1)
				   ,(make-onename "st"))
		       ,(make-onename "st"))
		,(make-onename "st")))



	`((,(make-name name-ent name_arch "-putst")
	      (quote ,(make_name_var_sig name_var1
					 bool_sig_var))
	    (setarrayi ,int1
		       (logbit ,int2
			       ,signed)
				  (,(make-name name-ent
					       name_arch
					       "-getst")
				   (quote ,name_var1)
					 ,(make-onename "st")))
	    ,(make-onename "st"))

	  ,@(slice-rec2 name-ent name_arch
			 name_var1
			 signed
			 max1
			 (1+ int1)
			 (1+ int2)
			 bool_sig_var)))
    (cw "Error on slice-rec2")))


(defun slice-rec1 (name-ent name_arch
		   name_var1
		   name_var2
		       max1
		       int1
		       max2
		       int2
		       bool_sig_var)
  (declare (xargs :measure (nfix (+ (- max1 int1)
				    (- max2 int2)))))
  (if (and (integerp max1) (integerp int1) (>= (- max1 int1) 0)
	   (integerp max2) (integerp int2) (>= (- max2 int2) 0))
      (if (and (= (nfix (- max1 int1)) 0)
	       (= (nfix (- max2 int2)) 0))

	  `((,(make-name name-ent name_arch "-putst")
	         (quote ,(make_name_var_sig name_var1
		 		            bool_sig_var))
	    (setarrayi ,int1
		       (getarrayi (,(make-name name-ent
					       name_arch
					       "-getst")
				    (quote ,name_var2)
				   ,(make-onename "st"))
				  ,int2)
		       (,(make-name name-ent name_arch "-getst")
			 (quote ,name_var1)
			,(make-onename "st")))
            ,(make-onename "st")))


 `((,(make-name name-ent name_arch "-putst")
      (quote ,(make_name_var_sig name_var1
				 bool_sig_var))
	    (setarrayi ,int1
		       (getarrayi (,(make-name name-ent
					       name_arch
					       "-getst")
				    (quote ,name_var2)
				   ,(make-onename "st"))
				  ,int2)
		       (,(make-name name-ent
				    name_arch
				    "-getst")
			(quote ,name_var1)
			,(make-onename "st")))

     ,(make-onename "st"))
   ,@(slice-rec1 name-ent name_arch
	         name_var1
	         name_var2
	         max1
	         (1+ int1)
	         max2
	         (1+ int2)
	         bool_sig_var)))
(cw "Error on slice-rec1")))


(defun slice-rec3 (name-ent name_arch
		   name_var1
		   name_var2
		   max1
		   int1
		   int2
		   bool_sig_var)
  (declare (xargs :measure (nfix (- max1 int1))))

  (if (and (integerp max1) (integerp int1) (>= (- max1 int1) 0)
	   (integerp int2))
      (if (and (= (nfix (- max1 int1)) 0))

	  `((,(make-name name-ent name_arch "-putst")
	        (quote ,(make_name_var_sig name_var1
					   bool_sig_var))
	      (setarrayi ,int1
			 (getarrayi (quote ,name_var2)
				    ,int2)
			 (,(make-name name-ent name_arch  "-getst")
				   (quote ,name_var1)
					 ,(make-onename "st")))
	      ,(make-onename "st")))


 `((,(make-name name-ent name_arch  "-putst")
      (quote ,(make_name_var_sig name_var1
				 bool_sig_var))
     (setarrayi ,int1
		(getarrayi (quote ,name_var2)
			   ,int2)
		(,(make-name name-ent name_arch "-getst")
		  (quote ,name_var1)
			,(make-onename "st")))
     ,(make-onename "st"))

   ,@(slice-rec3 name-ent name_arch
		 name_var1
		 name_var2
		 max1
		 (1+ int1)
		 (1+ int2)
		 bool_sig_var)))
(cw "Error on slice-rec3")))


(defun slice-rec4 (name-ent name_arch
		   name_var1
		   name_var2
		   max1
		   int1
		   symb
		   bool_sig_var)
  (declare (xargs :measure (nfix (- max1 int1))))

  (if (and (integerp max1) (integerp int1) (>= (- max1 int1) 0))
      (if (and (= (nfix (- max1 int1)) 0))

	  `((,(make-name name-ent name_arch "-putst")
	        (quote ,(make_name_var_sig name_var1
					   bool_sig_var))
	      (setarrayi ,int1
			 (getarrayi (quote ,name_var2)
				    ,symb)
			 (,(make-name name-ent name_arch  "-getst")
				   (quote ,name_var1)
					 ,(make-onename "st")))
	      ,(make-onename "st")))


 `((,(make-name name-ent name_arch  "-putst")
      (quote ,(make_name_var_sig name_var1
				 bool_sig_var))
     (setarrayi ,int1
		(getarrayi (quote ,name_var2)
			   ,symb)
		(,(make-name name-ent name_arch "-getst")
		  (quote ,name_var1)
			,(make-onename "st")))
     ,(make-onename "st"))

   ,@(slice-rec4 name-ent name_arch
		 name_var1
		 name_var2
		 max1
		 (1+ int1)
		 symb
		 bool_sig_var)))
(cw "Error on slice-rec4")))





;; function type_of
;; to  find the type of one element

(defun type_of (element list_of_mem_element list_of_types)
  (cond ((endp list_of_mem_element) "error on type_of")
        ((and (symbolp element) (equal element (car list_of_mem_element)))
          (change-to-const (car list_of_types)))
        ((and (symbolp element) (not (equal element (car list_of_mem_element))))
           (type_of element (cdr list_of_mem_element)
		                        (cdr list_of_types)))
        (t "error on type_of")))




(defun true_func (func$ rst)
   (cond ((consp rst) ;(list func$ type)
	  (cond ((not (equal (caddr rst) nil))
		 ;; operator with 3 args
		 (cons (list (nth (change-to-const (cdr (car rst)))
                            (nth (change-to-const func$) *true_function*))
                        (caar rst)
                        (car (cadr rst))
			(car (caddr rst)))
		       (change-to-const (cdr (car rst)))))

		 ((and (equal (caddr rst) nil)
		       (not (equal (cadr rst) nil)))
		  (cons (list (nth (change-to-const (cdr (car rst)))
				   (nth (change-to-const func$) *true_function*))
			      (caar rst)
			      (car (cadr rst)))
			(change-to-const (cdr (car rst)))))

		  (t (cons (list (nth (change-to-const (cdr (car rst)))
				   (nth (change-to-const func$) *true_function*))
			      (caar rst))
			(change-to-const (cdr (car rst)))))))


         (t "error on true_func")))


(mutual-recursion
(defun expand-exp (name-ent name_arch e list_of_mem_elmt list_types)
  (cond

   ((symbolp e)
      (cons `(,(make-name name-ent
		  name_arch
		  "-getst")
         (quote ,e)
	    ,(make-onename "st"))
          (type_of e list_of_mem_elmt list_types)))

   ((integerp e)
     (cons e *int*))

   ((consp e)
      (cond
	 ((equal (car e) 'index)
	  (cons `(getarrayi (,(make-name name-ent name_arch "-getst")
			     (quote ,(nth 1 e)) st) ,(nth 2 e))
                ;;(type_of (nth 1 e) list_of_mem_elmt list_types)))
		*bit*))

         (t ;; call of function$
           (true_func (car e)
	      (expand-exp-list name-ent name_arch (cdr e) list_of_mem_elmt list_types)))))

    (t "error in expand-exp")))


(defun expand-exp-list (name-ent name_arch list list_of_mem_elmt list_types)
  (if (consp list)
      (cons (expand-exp name-ent name_arch (car list) list_of_mem_elmt list_types)
	    (expand-exp-list name-ent name_arch (cdr list) list_of_mem_elmt list_types))
      nil)))

#|
(mutual-recursion
(defun expand-exp (name-ent name_arch e)
  (cond
   ((symbolp e)
    `(,(make-name name-ent
		  name_arch
		  "-getst")
      (quote ,e)
	    ,(make-onename "st")))
   ((consp e)
    (if (equal (car e) 'quote)
	e
        (cons (car e)
	      (expand-exp-list name-ent name_arch (cdr e)))))
   (t e)))
(defun expand-exp-list (name-ent name_arch list)
  (if (consp list)
      (cons (expand-exp name-ent name_arch (car list))
	    (expand-exp-list name-ent name_arch (cdr list)))
      nil)))
|#

(defun call_or_single_element (elmt)
  (cond ((consp elmt)
	 (cond ((= (length elmt) 1) (car elmt))
	       (t elmt)))
	(t elmt)))


(defun assignment (name-ent name_arch list bool_sig_var list_mem_elmt list_type)
  (cond ((and (consp (nth 0 list)) (equal (len (nth 0 list)) 4)
	      (consp (member 'index (nth 2 list)))
	      (equal (len (nth 2 list)) 4))
	 ; OP1 (deb1 to fin1) <= OP2 (deb2 to fin2)
         ; (index OP1 deb1 fin1) <= (index OP2 deb2 fin2)
	 (let ((op1 (cadr (nth 0 list)))
	       (op2 (cadr (nth 2 list)))
	       (deb1 (nth 2 (nth 0 list)))
	       (fin1 (nth 3 (nth 0 list)))
	       (deb2 (nth 2 (nth 2 list)))
	       (fin2 (nth 3 (nth 2 list))))
	   (slice-rec1 name-ent name_arch
		       op1
		       op2
		       fin1
		       deb1
		       fin2
		       deb2
		       bool_sig_var)))

	((and (consp (nth 0 list)) (equal (len (nth 0 list)) 4)
	      (consp (member 'index (nth 0 list)))
	      (consp (member 'index (nth 2 list)))
	      (equal (len (nth 2 list)) 3))

	 ; OP1 (deb1 to fin1) <= OP2 (fn i ..)
	 ; (index OP1 deb1 fin1) <= (index OP2 (fn i..))
	 (let* ((op1 (cadr (nth 0 list)))
	        (op2 (cadr (nth 2 list)))
	        (deb1 (nth 2 (nth 0 list)))
	        (fin1 (nth 3 (nth 0 list)))
		(range2 (nth 2 (nth 2 list))))

	   (slice-rec4  name-ent name_arch
			op1
			op2
			fin1
			deb1
			(call_or_single_element
                            (car (expand-exp name-ent
					name_arch
					range2
					list_mem_elmt
					list_type)))
			bool_sig_var)))

	((and (consp (nth 0 list)) (equal (len (nth 0 list)) 4)
	      (consp (member 'index (nth 0 list)))
	      (not (consp (member 'index (nth 2 list)))))
	      ; OP1 (deb1 to fin1) <= OP2
	      ; (index OP1 deb1 fin1) <= OP2
	      (let ((deb1 (nth 2 (nth 0 list)))
		    (fin1 (nth 3 (nth 0 list))))
		     (slice-rec1 name-ent name_arch
				  (nth 1 (nth 0 list))
				  (nth 2 list)
				  fin1
				  deb1
				  (- fin1 deb1)
				  0
				  bool_sig_var)))


	((and (consp (nth 0 list))
	      (consp (member 'index (nth 0 list)))
	      (equal (len (nth 0 list)) 3)
	      (consp (member 'index (nth 2 list)))
	      (equal (len (nth 2 list)) 3))

	 ; OP1 (fn i..) <= OP2 (fn i ..)
	 ; (index OP1 (fn i..)) <= (index OP2 (fn i..))
	 (let ((op1 (nth 1 (nth 0 list)))
	       (op2 (nth 1 (nth 2 list)))
	       (range1
   (call_or_single_element (car (expand-exp name-ent
				       name_arch
				       (nth 2 (nth 0 list))
				       list_mem_elmt
				       list_type))))
	       (range2
  (call_or_single_element (car (expand-exp name-ent
				      name_arch
				      (nth 2 (nth 2 list))
				      list_mem_elmt
				      list_type)))))
	   `((,(make-name name-ent name_arch "-putst")
	      (quote ,(make_name_var_sig op1
					 bool_sig_var))
	      (setarrayi ,range1
			 (getarrayi (quote ,op2)
				    ,range2)
			 (,(make-name name-ent name_arch  "-getst")
			  (quote ,op1)
			  ,(make-onename "st")))
	      ,(make-onename "st")))))


	((and (consp (nth 0 list))
	      (consp (member 'index (nth 0 list)))
	      (equal (len (nth 0 list)) 3)
	      (not (consp (member 'index (nth 2 list)))))

	 ; OP1 (fn i ..) <= (fn2 ...)
         ; (index OP1 (fn i ..)) <= (fn2 i ..)
	 (let ((op1 (nth 1 (nth 0 list)))
	       (op2 (car (expand-exp name-ent
				name_arch
				(nth 2 list)
				list_mem_elmt
				list_type)))
	       (range1
  (call_or_single_element (car (expand-exp name-ent
				      name_arch
				      (nth 2 (nth 0 list))
				      list_mem_elmt
				      list_type)))))
	   `((,(make-name name-ent name_arch "-putst")
	    (quote ,(make_name_var_sig op1
				       bool_sig_var))
	    (setarrayi ,range1
		       ,op2
		       (,(make-name name-ent name_arch  "-getst")
			(quote ,op1)
			,(make-onename "st")))
	    ,(make-onename "st")))))

	((and (consp (nth 0 list))
	      (consp (member 'index (nth 0 list)))
	      (equal (len (nth 0 list)) 4)
	      (integerp (nth 2 list)))

	 ; OP1 (deb1 to fin1) <= 4; <- signed-byte
	 ; (index OP1 deb1 fin1) <= 4
	 (let ((op1 (nth 1 (nth 0 list)))
	       (op2 (nth 2 list))
	       (deb1 (nth 2 (nth 0 list)))
	       (fin1 (nth 3 (nth 0 list))))

	   (slice-rec2 name-ent name_arch
			op1
			op2
			fin1
			deb1
			0
			bool_sig_var)))

;;
	((and (consp (nth 0 list))
	      (consp (member 'index (nth 0 list)))
	      (equal (len (nth 0 list)) 4)
	      (integerp (nth 2 list)))

	 ; OP1 (deb1 to fin1) <= (fn ....)
	 ; (index OP1 deb1 fin1) <= (fn ..)
	 (let* ((op1 (nth 1 (nth 0 list)))
		(op2 (car (expand-exp name-ent
				 name_arch
				 (nth 2 list)
				 list_mem_elmt
				 list_type)))
		(deb1 (nth 2 (nth 0 list)))
		(fin1 (nth 3 (nth 0 list)))
		(instr (slice-rec3 name-ent name_arch
				   op1
				   (make-onename "temp")
				   fin1
				   deb1
				   0
				   t)))
	 `((let ((,(make-onename "temp")
		     ,op2))
		    (seq st,@instr)
		    )
	       ,(make-onename "st"))))


       ((and (consp (nth 0 list))
	     (consp (member 'index (nth 0 list)))
	      (equal (len (nth 0 list)) 3)
	      (not (consp (member 'index (nth 0 list)))))
	 ; OP1 (fn i..) <= OP2;
	 ; (index OP1 (fn i ..)) <= OP2
	 (let ((op1 (nth 1 (car list)))
	       (op2 (car (expand-exp name-ent
				name_arch
				(nth 2 list)
				list_mem_elmt
				list_type)))
	       (range1 (car (expand-exp name-ent
				   name_arch
				   (nth 2 (car list))
				   list_mem_elmt
				   list_type))))

	   `((,(make-name name-ent name_arch "-putst")
	      (quote ,(make_name_var_sig op1
					 bool_sig_var))
	      (setarrayi ,(call_or_single_element range1)
			 ,op2
			 (,(make-name name-ent name_arch "-getst")
			  (quote ,op1)
			  ,(make-onename "st")))
	     ,(make-onename "st")))))


	((and (not (consp (nth 0 list)))
	      (equal (len (nth 2 list)) 4)
	      (consp (member 'index (nth 2 list))))
	 ; OP1<= OP2 (deb to fin)
         ; OP1 <= (index OP2 deb fin)
	 (let* ((op1 (car list))
		(op2 (nth 1 (nth 2 list)))
		(deb2 (nth 2 (nth 2 list)))
		(fin2 (nth 3 (nth 2 list))))
	   (slice-rec1 name-ent name_arch
			op1
			op2
			(- fin2 deb2)
			0
			fin2
			deb2
			bool_sig_var)))


	((and (not (consp (nth 0 list)))
	      (equal (len (nth 2 list)) 3)
	      (consp (member 'index (nth 2 list))))
	 ; OP1 <= OP2 (fn i..)
         ; OP1 <= (index OP2 (fn i..))
	 `((,(make-name name-ent name_arch "-putst")
	    (quote ,(make_name_var_sig (car list)
				       bool_sig_var))
	    (getarrayi (,(make-name name-ent
				    name_arch
				    "-getst")
			(quote ,(nth 1 (nth 2 list)))
			,(make-onename "st"))
		       ,(call_or_single_element (nth 2 (nth 2 list)))
	    ,(make-onename "st")))))


	((and (symbolp (car list)) (equal (length list) 3)
	      (symbolp (nth 2 list)))
	 ; A <= B
	 (let ((op1 (nth 0 list))
	       (op2 (nth 2 list)))
	  `((,(make-name name-ent name_arch "-putst")
	     (quote ,(make_name_var_sig op1
					bool_sig_var))
	     (,(make-name name-ent name_arch "-getst")
	      (quote ,op2)
	      ,(make-onename "st"))
	     ,(make-onename "st")))))


	((and (symbolp (car list)) (equal (length list) 3))
	 ; A <= (fn ...)
	 (let ((op1 (nth 0 list))
	       (op2 (car (expand-exp name-ent
				name_arch
				(nth 2 list)
				list_mem_elmt
				list_type))))
	   `((,(make-name name-ent name_arch "-putst")
	      (quote ,(make_name_var_sig op1
					 bool_sig_var))
	      ,op2
	      ,(make-onename "st")))))

	(t (cw "Syntax error on assignment"))))


(mutual-recursion
(defun if-statement (name-ent name-arch instr list_mem_elmt list_type)
  (if (endp instr)
      nil
	 (let* ((instr_then (let-instructions name-ent
					      name-arch
					      (caddr instr)
					      list_mem_elmt list_type))
	       (instr_else (let-instructions name-ent
					     name-arch
					     (cadddr instr)
					     list_mem_elmt list_type))
	       (cond_stat (car (list (car (expand-exp-list name-ent name-arch
						      (list (nth 1 instr))
						      list_mem_elmt list_type
						      ))))))

	   (cond
	    ((equal instr_then nil)

	      `((if ,(car cond_stat)
		    ,(make-onename "st")
		  (seq ,(make-onename "st")
		     ,@instr_else)))

	      )

	    ((equal instr_else nil)

	     `((if ,(car cond_stat)
		 (seq ,(make-onename "st")
		     ,@instr_then)
		   ,(make-onename "st"))))

	    (t

	     `((if ,(car cond_stat)
		 (seq ,(make-onename "st")
		      ,@instr_then)
		 (seq ,(make-onename "st")
		     ,@instr_else)
		   )))))))


(defun let-instructions (name-ent name-arch list list_mem_elmt list_type)
 (if (endp list)
      nil
    (let ((instr (car list)))
      (cond

       ; clause0 : "for" statement
       ((not (equal (member-eq 'for-loop instr)
		    nil))
	(let ((num (cadr instr)))

	`((,(make-name ""
			"for-loop"
			(natural-to-string num))
	    ,(make-onename "st"))
	     ,@(let-instructions name-ent name-arch
				 (cdr list) list_mem_elmt list_type)))

       ) ; end clause0


       ; clause1 : "if"  statement

       ((not (equal (member-eq 'if instr)
		     nil))

	(let ((new_list (if-statement name-ent
				      name-arch
				      instr
				      list_mem_elmt list_type)))

	 `(,@new_list
	     ,@(let-instructions name-ent name-arch
				 (cdr list) list_mem_elmt list_type)))


       ) ; end clause1

         ; clause2 : variable assignment
        ((not (equal (member-eq ':= instr)
		     nil))

	 (let ((new_list (assignment name-ent
				     name-arch
				     instr
				     nil
				     list_mem_elmt list_type)))


	 `(,@new_list
	     ,@(let-instructions name-ent name-arch
				 (cdr list) list_mem_elmt list_type)))


	 ) ; end clause2

	; clause2bis : C  variable assignment
        ((not (equal (member-eq '= instr)
		     nil))

	 (let ((new_list (assignment name-ent
				     name-arch
				     instr
				     nil
				     list_mem_elmt list_type)))


	 `(,@new_list
	     ,@(let-instructions name-ent name-arch
				 (cdr list) list_mem_elmt list_type)))


	 ) ; end clause2bis


	; clause3 : signal assignment
	((not (equal (member-eq '<= instr)
		     nil))

	 (let ((new_list (assignment name-ent
				     name-arch
				     instr
				     t
				     list_mem_elmt list_type)))


	 `(,@new_list
	     ,@(let-instructions name-ent name-arch
				 (cdr list) list_mem_elmt list_type)))

	 ) ; end clause3



  (t (cw "error on instruction ~p0~%" instr)))))))


(defun update-st-for-function (name-ent arch_name args)
  (let ((name_putst (make-name name-ent arch_name "-putst"))
	(name_make-state (make-name name-ent arch_name "-make-state")))
    (if (endp args)
	`(,name_make-state)
      `(,name_putst (quote ,(car args))
		     (list ,(car args))
	(,@(update-st-for-function name-ent arch_name (cdr args)))))))


(defun make-functions (list_of_functions
		       channel list_mem_elmt list_type
		       state)
  (declare (xargs :stobjs state
		 :mode :program))
  (if (endp list_of_functions)
      state
    (let* ((func (car list_of_functions))
	   (name (cadr_assoc_keyword :name func))
	   (arg (cadr_assoc_keyword :arg func))
	   (type_arg (cadr_assoc_keyword :type_args func))
	   (loc_var (cadr_assoc_keyword :local_variables func))
	   (loc_var_type (cadr_assoc_keyword :local_variables_type func))
	   (type_return (list (cadr_assoc_keyword :type_return func)))
	   (body (cadr_assoc_keyword :body func))
	   (new_name (intern (string name) "ACL2"))
	   (state
	    (fms "~%;*****  Modelisation of the VHDL function ~x0 *****
;Definition of the local memory state"
		 (list (cons #\0 new_name))
		 channel
		 state
		 nil))

	   (state
	    (make-get-nth 'fct- new_name
			  arg
			  nil
			  (append loc_var
				  (list 'return))
			  nil
			  nil
			  channel
			  state))

	   (state
	    (make-getst-putst 'fct- new_name
			      arg
			      nil
			      (cons 'return loc_var)
			      nil
			      nil
			      channel
			      state))
	   (state
	    (make-state-p 'fct- new_name
			  (append arg
				  loc_var
				  '(return))
			  (append type_arg
				  loc_var_type
				  type_return)
			  channel
			  state))
	   (state
	    (make-update-state 'fct- new_name
			       channel
			       state))
	   (state
	    (make-make-state 'fct- new_name
			     (append arg
				     loc_var
				     (list 'return))
			     (append type_arg
				     loc_var_type
				     type_return)
			     nil
			     nil
			     nil
			     channel
			     state))
	   (new_instr (let-instructions 'fct- new_name
					body list_mem_elmt list_type))
	   (state
(fms
"~% ;;; Main function
(defun ~x0 ~x1
  (let* ((st ~x3)
	 (st ~x4))
    ~x5))~%"
(list (cons #\0 new_name)
      (cons #\1 arg)
      (cons #\3 (update-st-for-function 'fct- new_name
					arg))
      (cons #\4 `(seq st ,@new_instr))
      (cons #\5 `(,(make-name 'fct- new_name "-getst")
		 'return
		  st)))
channel
state
nil)))
(make-functions (cdr list_of_functions)
		channel list_mem_elmt list_type
		state))))





(defun make-for-loop (name-ent name_arch
		      list_of_for
		      channel list_mem_elmt list_type
		      state)
  (declare (xargs :stobjs state
		 :mode :program))

  (let* ((instr_for (car list_of_for))
	 (name_for (car instr_for))
	 (range (cadr instr_for))
	 (range1 (car range))
	 (range2 (cadr range))
	 (instr (caddr instr_for))
	 (new_instr (let-instructions name-ent name_arch
				      instr list_mem_elmt list_type)))

    (if (< range1 range2)  ;; ascending loop

	(fms "~%;; This function represents the for loop ~x0 ;;;;;;;~%
(defun ~x0 (i j st)
  (declare (type integer i)
	   (type integer j)
	   (type cons st)
	   (xargs :measure (nfix (- j i))))
  (if (zp (- j i))
      st
(~x0 (1+ i)
     j
     ~x1))) ~%"
(list
(cons #\0 (make-onename name_for))
(cons #\1 `(seq st ,@new_instr)))
channel
state
nil)


(fms "~%;; This function represents the for loop ~x0 ;;;;;;;~%
(defun ~x0 (i j st)
  (declare (type integer i)
	   (type integer j)
	   (type cons st)
	   (xargs :measure (nfix (- i j))))
  (if (zp (- i j))
      st
    (~x0 (1+ i)
	  j
	 ~x1))) ~%"
(list
(cons #\0 (make-onename name_for))
(cons #\1 `(seq st ,@new_instr)))
channel
state
nil))))


(defun process-functions (name-ent name_architecture
			  list_of_process
		     channel list_mem_elmt list_type state)
  (declare (xargs :stobjs state
		 :mode :program))

(if (endp list_of_process)
    state
  (let* ((new_instr (let-instructions name-ent name_architecture
				      (cadr (car list_of_process))
				      list_mem_elmt list_type))
	(state
(fms "~%;; This function represents the process ~x0 ;;;;;;;~%
(defun ~x1 (st) ~x2)"
(list
(cons #\0 (caar list_of_process))
(cons #\1 (make-name (concatenate 'string
				  (string name-ent)
				  (string name_architecture)
				  "-")
		     (caar list_of_process)
	             "-cycle"))
;(cons #\2 (make-name name-ent name_architecture "-stp"))

(cons #\2 (append '(seq st) new_instr)))


channel
state
nil)))

(process-functions name-ent name_architecture
		   (cdr list_of_process)
		   channel list_mem_elmt list_type
		   state))))





(defun make-rec-comb-process (name-ent
			      name_arch
			      list_of_comb_process
			      channel
			      state)
  (declare (xargs :stobjs state
		  :mode :program))

  (if (endp list_of_comb_process)
      state

    (let* ((name_process (make-name (concatenate 'string
						 (string name-ent)
						 (string name_arch)
						 "-")
				    (string (caar list_of_comb_process))
				    "-cycle"))
       (state
    (fms "~%~%;;======== Function rec-comb-process ~x0  =====~%~%
(defun ~x0 (i st) ~%
  (cond ((zp i) st)
	(t (~x0 (1- i) ~x1)))) ~%"

(list
(cons #\0 (make-name (concatenate 'string
				  (string name-ent)
				  (string name_arch)
				  "-")
		     (string (caar list_of_comb_process))
	             "-rec-cycle"))
(cons #\1 (append '(seq st) (list (list name_process 'st)))))
channel
state
nil)))
(make-rec-comb-process name-ent
			name_arch
			(cdr list_of_comb_process)
			channel
			state))))



(defun let-update-signals (name-ent name-arch list)
  (if (endp list)
      nil
    (let ((sig (car list)))
      `((,(make-name name-ent name-arch
		      "-putst")
	  (quote ,sig)
		(,(make-name name-ent
			     name-arch
			     "-getst")
		 (quote ,(make-name ""
				   sig
				   "+"))
		         ,(make-onename "st"))
		,(make-onename "st"))
	,@(let-update-signals name-ent name-arch (cdr list))))))


(defun comp-updt_sig-rec_in (name-ent name-arch
			  name-comp name_instance
			  links_inputs)
  (if (endp links_inputs)
      nil
    (let ((name-putst-arch (make-name name-ent
				 name-arch
				 "-putst"))
	  (name-getst-arch (make-name name-ent
				 name-arch
				 "-getst"))
	  (name-putst-comp (make-name ""
				 name-comp
				 "-putst"))
          (first_link (car links_inputs)))
      (if (not (consp (car first_link)))

  ; architecture -> input of component
	  (let ((src (make-name "" (string (car first_link)) ""))
                (dest (cadr first_link)))

   `((,name-putst-arch
      (quote ,name_instance)
       (,name-putst-comp (quote ,dest)
			 (,name-getst-arch (quote ,src)
					   ,(make-onename "st"))
			 (,name-getst-arch (quote ,name_instance)
					   ,(make-onename "st")))
       ,(make-onename "st"))
     ,@(comp-updt_sig-rec_in name-ent name-arch
			 name-comp name_instance
			 (cdr links_inputs))))


	     ;; array -> one element

	  (let ((src (make-name "" (string (nth 1 (car first_link))) ""))
                (dest (make-name "" (string (nth 1 first_link)) "")))



   `((,name-putst-arch
      (quote ,name_instance)
       (,name-putst-comp (quote ,dest)
			 (getarrayi (,name-getst-arch (quote ,src)
						      ,(make-onename "st"))
				    ,(nth 2 (car first_link)))
			 (,name-getst-arch (quote ,name_instance)
					   ,(make-onename "st")))
       ,(make-onename "st"))
     ,@(comp-updt_sig-rec_in name-ent name-arch
			 name-comp name_instance
			 (cdr links_inputs))))))))



(defun comp-updt_sig-rec_out (name-ent name-arch
			  name-comp name_instance
			  links_outputs)
  (if (endp links_outputs)
      nil
    (let ((name-putst-arch (make-name name-ent
				 name-arch
				 "-putst"))
	  (name-getst-arch (make-name name-ent
				 name-arch
				 "-getst"))
	  (name-getst-comp (make-name ""
				 name-comp
				 "-getst"))
          (first_link (car links_outputs)))
      (if (not (consp (car first_link)))

	  (let ((dest (make-name "" (string (car first_link)) ""))
                (src (make-name "" (string (cadr first_link)) "")))

   `((,name-putst-arch
     (quote ,src)
     (,name-getst-comp (quote ,dest)
		       (,name-getst-arch (quote ,name_instance)
					 ,(make-onename "st")))
      ,(make-onename "st"))
    ,@(comp-updt_sig-rec_out name-ent name-arch
			 name-comp name_instance
			 (cdr links_outputs))))


	     ;; array -> one element

	  (let ((dest (make-name "" (string (nth 1 (car first_link))) ""))
                (src (make-name "" (string (nth 1 first_link)) "")))

   `((,name-putst-arch (quote ,dest)
	               (setarrayi ,(nth 2 (car first_link))
                          (,name-getst-comp (quote ,src)
					    (,name-getst-arch (quote ,name_instance)
					                   ,(make-onename "st")))
                            (,name-getst-arch (quote ,dest) ,(make-onename "st")))
	        ,(make-onename "st"))
    ,@(comp-updt_sig-rec_out name-ent name-arch
			 name-comp name_instance
			 (cdr links_outputs))))))))



(defun find_links_input (inputs links)
  (cond ((endp links) nil)
	(t
	 (let* ((one_links (car links))
		(one_sig (cadr one_links)))
	   (if (member one_sig inputs)
	       (cons (car links)
		     (find_links_input inputs (cdr links)))

	      (find_links_input inputs (cdr links)))))))



(defun find_links_output (outputs links)
  (cond ((endp links) nil)
	(t
	 (let* ((one_links (car links))
		(one_sig (cadr one_links)))
	   (if (member one_sig outputs)
	       (cons (car links)
		     (find_links_output outputs (cdr links)))

	      (find_links_output outputs (cdr links)))))))


(defun search_input_comp (name_comp list_of_components)
  (let ((car_list_of_components (car list_of_components)))
  (cond ((endp list_of_components) nil)
	((equal name_comp (car car_list_of_components))
	 (append (cadr_assoc_keyword :inputs_signals (cdr car_list_of_components))
		 (cadr_assoc_keyword :generic_parameters (cdr car_list_of_components))))
	(t (search_input_comp name_comp (cdr list_of_components))))))


(defun search_output_comp (name_comp list_of_components)
  (let ((car_list_of_components (car list_of_components)))
  (cond ((endp list_of_components) nil)
	((equal name_comp (car car_list_of_components))
	 (cadr_assoc_keyword :outputs_signals (cdr car_list_of_components)))
	(t (search_output_comp name_comp (cdr list_of_components))))))


(defun components-update-signals (name-ent name-arch
				  list_of_components
				  list_of_configurations
				  list_of_links)
  (if (endp list_of_configurations)
      nil
    (let* ((comp (car list_of_configurations))
	   (name_comp (make-name (caddr comp) (cadddr comp) ""))
           (name_instance (make-name "" (car comp) ""))
	   (name_component (cadr comp))

	   (inputs_of_comp (search_input_comp name_component list_of_components))
	   (outputs_of_comp (search_output_comp name_component list_of_components))

	   (links_inputs (find_links_input inputs_of_comp (cdr (car list_of_links))))
	   (links_outputs (find_links_output outputs_of_comp (cdr (car list_of_links))))

	   (new_list1 (comp-updt_sig-rec_in name-ent name-arch
					name_comp name_instance
					links_inputs))
	  (new_list2 (comp-updt_sig-rec_out name-ent name-arch
					name_comp name_instance
					links_outputs)))
      `(,@new_list1 ,@new_list2
	 ,@(components-update-signals name-ent name-arch
				      list_of_components
				    (cdr list_of_configurations)
				    (cdr list_of_links))))))


#|
(defun components-update-signals (name-ent name-arch
				  list_of_configurations
				  list_of_links)
  (if (endp list_of_configurations)
      nil
    (let* ((comp (car list_of_configurations))
	   (name_comp (make-name (cadr comp) (caddr comp) ""))
           (name_instance (make-name "" (car comp) ""))
	   (links_inputs (car (cdr (car list_of_links))))
	   (links_outputs (cadr (cdr (car list_of_links))))
	   (new_list1 (comp-updt_sig-rec_in name-ent name-arch
					name_comp name_instance
					links_inputs))
	  (new_list2 (comp-updt_sig-rec_out name-ent name-arch
					name_comp name_instance
					links_outputs)))
      `(,@new_list1 ,@new_list2
	 ,@(components-update-signals name-ent name-arch
				    (cdr list_of_configurations)
				    (cdr list_of_links))))))
|#


(defun make-update-of-components (name-ent name_arch list_of_configurations)
  (if (endp list_of_configurations)
      nil
    (let* ((comp (car list_of_configurations))
         (name_comp (make-name (caddr comp) (cadddr comp) ""))
         (name_instance (make-name "" (car comp) "")))
      `((,(make-name name-ent name_arch "-putst")
	      (quote ,name_instance)
	      (,(make-name "" name_comp "-update-signals")
		     (,(make-name name-ent name_arch "-getst")
		      (quote ,name_instance)
		      st))
	      st)
	  ,@(make-update-of-components name-ent name_arch (cdr list_of_configurations))))))

(defun make-update-signals (name-ent name_architecture
			    list_of_locals_signals_and_outputs
			    list_of_components
		            list_of_configurations
			    list_of_links
		            channel state)
  (declare (xargs :stobjs state
		  :mode :program))

  (let* ((newinstr1 (let-update-signals name-ent name_architecture
				       list_of_locals_signals_and_outputs))
	 (newinstr2 (make-update-of-components name-ent name_architecture list_of_configurations))
	(newinstr3 (components-update-signals name-ent name_architecture
					      list_of_components
					      list_of_configurations
					      list_of_links)))

  (fms "~%~%;;======== Function update of signals  =====~%~%
(defun ~x0 (st) ~x2) ~%"
; (declare (xargs :guard (~x1 st)))
(list
(cons #\0 (make-name name-ent name_architecture "-update-signals"))
(cons #\1 (make-name name-ent name_architecture "-stp"))
(cons #\2 (append '(seq st)
		  newinstr1
	          newinstr2
		  newinstr3)))

channel
state
nil)))


(defun name_of_process (name-ent name-arch list_of_process)
  (if (endp list_of_process)
      nil
    `((,(make-name (concatenate 'string
    			   (string name-ent)
			       (string name-arch)
			       "-")
		  (caar list_of_process)
		  "-cycle")
       ,(make-onename "st"))
	  ,@(name_of_process name-ent name-arch (cdr list_of_process)))))



(defun name_of_conc_statem (name-ent name-arch list_of_conc_stat)
  (if (endp list_of_conc_stat)
      nil
    (let ((name-update-sig (make-name name-ent name-arch "-update-signals")))
    `((,name-update-sig (,(make-name (concatenate 'string
    			   (string name-ent)
			       (string name-arch)
			       "-")
		  (caar list_of_conc_stat)
		  "-cycle")
       ,(make-onename "st")))
	  ,@(name_of_conc_statem name-ent name-arch (cdr list_of_conc_stat))))))



(defun make-cycle-of-components (name-ent name_arch list_of_configurations)
  (if (endp list_of_configurations)
      nil
    (let* ((comp (car list_of_configurations))
	   (name_comp (make-name (caddr comp) (cadddr comp) ""))
           (name_instance (make-name "" (car comp) "")))
      `((,(make-name name-ent name_arch "-putst")
	      (quote ,name_instance)
	      (,(make-name "" name_comp "-cycle")
		     (,(make-name name-ent name_arch "-getst")
		      (quote ,name_instance)
		      st))
	      st)
	  ,@(make-cycle-of-components name-ent name_arch (cdr list_of_configurations))))))



(defun make-rec-concurrent-stat (name-ent name_architecture
				 concurrent-stat channel state)
     (declare (xargs :stobjs state
		  :mode :program))
  (cond ((endp concurrent-stat) state)
	(t (let ((name_conc (name_of_conc_statem name-ent name_architecture concurrent-stat)))

(fms "~%~%;;======== Function rec-concurrent-stat  =====~%~%
(defun ~x0 (i st) ~%
  (cond ((zp i) st)
	(t (~x0 (1- i) ~x1)))) ~%"

(list
(cons #\0 (make-name name-ent name_architecture "-rec-conc-stat"))
(cons #\1 (append '(seq st) name_conc)))
channel
state
nil)))))




(defun form-rec-concurrent-stat-name (name-ent name_architecture i)
  `((,(make-name "" (concatenate 'string
                   (string name-ent)
			       (string name_architecture)
			       "-")
		  "rec-conc-stat")
    ,i
       ,(make-onename "st"))))


(defun number_of_signal_ass (list)
  (cond ((endp list) 0)
	(t
	 (if (consp (member '<= (car list)))
	     (1+ (number_of_signal_ass (cdr list)))
	   (number_of_signal_ass (cdr list))))))

;; form call to recursive functions for comb process
(defun make-call-of-comp (name-ent name_arch list_of_comb_process)
  (cond ((endp list_of_comb_process)
	 nil)
	 (t
	  (let ((number_of_instr (number_of_signal_ass (cadar list_of_comb_process)))
	       (name-func (make-name (concatenate 'string
						  (string name-ent)
						  (string name_arch)
						  "-")
				     (caar list_of_comb_process)
				     "-rec-cycle")))
	   `((,name-func ,number_of_instr st)
	     ,@(make-call-of-comp name-ent
				  name_arch
				  (cdr list_of_comb_process)))))))



(defun make-cycle (name-ent name_architecture
		   list_of_process
		   list_of_comb_process
		   list_of_configurations
		   nat
		   channel
		   state)
    (declare (xargs :stobjs state
		  :mode :program))
    (let ((list (name_of_process name-ent name_architecture
				 list_of_process))
	  (comp (make-cycle-of-components name-ent name_architecture list_of_configurations))
	  (rec-conc-stat (if (equal nat nil)
			     nil
			   (form-rec-concurrent-stat-name name-ent
			  name_architecture nat)))
	  (make-call-of-comb-process (make-call-of-comp name-ent
							 name_architecture
							 list_of_comb_process))
	  )




(fms "~%~%;;======== Function cycle of simulation  =====~%~%
(defun ~x0 (st) ~% ~x2) ~%"

(list
(cons #\0 (make-name name-ent name_architecture "-cycle"))
(cons #\2 (append '(seq st) list rec-conc-stat make-call-of-comb-process comp)))
channel
state
nil)
))


(defun make-simul (name-ent name_architecture
		   channel
		   state)

  (declare (xargs :stobjs state
		  :mode :program))

  (let ((name-simul (make-name name-ent name_architecture "-simul"))
	(name-cycle (make-name name-ent name_architecture "-cycle"))
	(name-update-sig (make-name name-ent name_architecture "-update-signals")))

  (fms "~%~%;;======== Function for N simulation cycles  =====~%~%
(defun ~x0 (n st)
   (if (zp n)
      st
    ~x2)) ~%~%~%~% "
; (declare (xargs :guard (~x1 st)))
(list
(cons #\0 name-simul)
(cons #\1 (make-name name-ent name_architecture "-stp"))
(cons #\2 `(,name-simul (1- n)
			(,name-cycle
			 (,name-update-sig st)))))

channel
state
nil)))