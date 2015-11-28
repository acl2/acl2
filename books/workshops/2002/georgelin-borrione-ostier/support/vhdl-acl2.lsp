;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                                                                          ;
;   Written by : Philippe Georgelin                                        ;
;   Email : Philippe.Georgelin@st.com                                     
;                           
; $Id: vhdl-acl2.lisp,v 1.29 2002/05/02 12:29:52 gp34 Exp $                                                          ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")
(include-book "acl2-transl")


(set-acl2-print-case :downcase)
(set-ignore-ok t) 
(set-state-ok t)
;;; Modified 12/24/2014 to avoid the nu-rewriter, which is being eliminated.
;;; (set-nu-rewriter-mode nil); nu-rewriter mode off

(program)


(defun nifconvert (in_filename out out-thm state)
  (mv-let (channel state)
	  (open-input-channel in_filename :object state)
	 
	  (if channel
	      (mv-let (eofp obj state)
		      (read-object channel state)
		      (cond
		       (eofp 
			(mv (list "EMPTY") state)) ;; empty file)		       
			(t 			  
			 (seq-mv (
				  (state (close-input-channel channel state))
				  (state (create-definition-file obj out state))
				  (state (create-theorem-file obj out-thm state)))
				 (mv (list t) state)))))
		      
	   (mv (list "NOEXIST") state);; no existing file
	   )))


;; to write content into a file
(defun write_file (file content state)
  (mv-let (channel state)
	  (open-output-channel (string-downcase (string file)) :object state)
	  (pprogn
	   (fms "~x0"
		(list (cons #\0 content))
		channel
		state
		nil)
	   (close-output-channel channel state))))


(defun read-obj (state)
      (mv-let
         (eof-read obj state)
	 (read-object *standard-ci* state)
	 (declare (ignore eof-read))
     (mv obj state)))



(defun create-output-files (string list state)
  (declare (xargs :guard (stringp string)))
  (let ((path (get-global 'connected-book-directory state)))
            (let ((state
		    (create-definition-file list 
					    (concatenate 'string path
							 string
							 ".lisp")
					    state)))

	       (let ((state
(fms "~%~% -------  File ~x0 generated -------- ~%"
     (list (cons #\0 (concatenate 'string 
				  string
				  ".lisp")))
                     *standard-co*
                     state
                     nil)))
(let ((state (create-theorem-file list                                   
				  (concatenate 'string path string "-thm.lisp")
				  state)))
  (let ((state
	 (fms "------  File ~x0 generated ------- ~%"
	      (list (cons #\0 (concatenate 'string
					   string
					   "-thm.lisp")))
	      *standard-co*
	      state
	      nil)))
		 state))))))



;; open-in-channel (* state) -> (mv * state)

(defun open-in-channel (string state)
  (declare (xargs :guard (stringp string)))
  (let ((path (get-global 'connected-book-directory state)))
  (mv-let (channel state)
	  (open-input-channel (concatenate 'string path
					   string
					   ".nif")
					   :object state)
	  (if channel
	   (mv-let (eofp obj state)
		   (read-object channel state)
		   (cond
		    (eofp 
		     (let ((state 
			    (fms 
			     "~% ERROR : File empty ~%"
			       nil
			       *standard-co*
			       state 
			       nil)))
		       (mv nil state)))		       
		    (t 
		     (let ((state 
		         (close-input-channel channel state)))
		       (mv obj state)))))
	   
           (let ((state 
                  (fms 
                   "~% ERROR : Nif file not present ~%"
                   nil
                   *standard-co*
                   state 
                   nil)))
             (mv nil state))))))



(defun load-desc-file (string state)
(let* ((state
        (fms "~%Opening ~x0...~%" (list (cons #\0 string)) 
            *standard-co* state nil))
        (state
       (mv-let (a b state)
	  (ld-fn (list (cons 'standard-oi (concatenate 'string
						       string
						       ".lisp"))
		       (cons 'standard-co "log-output")
		       (cons 'proofs-co "log-proofs")			
		       (cons 'ld-error-action :return))
			 state t)
	  (declare (ignore a b))
		  state))
      (state
       (mv-let (a b state)
	  (ld-fn (list (cons 'standard-oi (concatenate 'string
						       string
						       "-thm.lisp"))
		       (cons 'standard-co "log-output")
		       (cons 'proofs-co "log-proofs")			
		       (cons 'ld-error-action :return))
			 state t)
	  (declare (ignore a b))
		  state)))
  state))



(defun choose-inputs-fn (list_inputs list_of_value list_types state)
  (if (endp list_inputs)
      (mv list_of_value state)
    (let ((state
	   (fms "~x0 (~x1) : "
	  (list (cons #\0 (car list_inputs))
		(cons #\1 (car list_types)))
	  *standard-co*
	  state
	  nil)))
      (mv-let (s state)
	      (read-obj state)
	      (choose-inputs-fn (cdr list_inputs)
				(append list_of_value
					(list s))
				(cdr list_types)
				state)))))


(defun coerce-fn (string i vec)
  (if (zp i)
      (case (char string i)
	  (#\1
	   (setarrayi 0 1 vec))
	  (#\0
	   (setarrayi 0 0 vec)))
    (case (char string i)
	  (#\1
	   (coerce-fn string 
		      (1- i)
		      (setarrayi i 1 vec)))
	  (#\0
	   (coerce-fn string 
		      (1- i)
		      vec)))))



(defun my-ev (form state)
   (er-let* ((pair (simple-translate-and-eval
                 form nil nil "A top-level form" 'top-level (w state) state)))
         (value (cdr pair))))


      
(defun one_element (elmt)
  (cond ((atom elmt) elmt)
	((consp elmt) (car elmt))
	(t "error on one_element")))


(defun one_symbolp (form)
    (cond ((endp form) nil)
	   ((and (symbolp (car form))
		 (not (equal (car form) 't))
	         (not (equal (car form) 'nil)))
		   t)
	   (t (one_symbolp (cdr form)))))


(defun symbolicp (form_list)
    (cond ((endp form_list) nil)
	    ((atom (car form_list))
	     (if (and (symbolp (car form_list))
			 (not (equal (car form_list) 't))
			 (not (equal (car form_list) 'nil)))
		    t
		    (symbolicp (cdr form_list))))
	    ((listp (car form_list))
		(if (one_symbolp (car form_list))
		    t
		    (symbolicp (cdr form_list))))
	    (t "Type Error on symbolicp")))


(defun change_view_of_vec (L int len_total new_vec)
  (cond ((zp L) new_vec)
        ((or (symbolicp len_total) (equal len_total nil))
            int) 
	(t (change_view_of_vec (1- L)
			       int
			       len_total
			       (cons (logbit (- len_total L) int) 
				     new_vec)))))


(defun change-view (list name_var state)
  (declare (xargs :stobjs state 
		  :mode :program))
  (if (endp list)
      state
;     (cond ((and (integerp (car list)) (consp (car type_var))) ;; bit-vector
; 	   (seq-mv (
; 		    ((e1 len_type state)
; 		    (my-ev (nth 2 (car type_var)) state)
; 		    (declare (ignore e1)))
; 		    (state
; 		     (fms "~t2 ~x0 ~tc : ~x1"
; 		       (list (cons #\0 (one_element (car name_var)))
; 			     (cons #\1 
;                                    (change_view_of_vec len_type 
; 							   (car list)
; 							   len_type
; 							   nil))
; 			     (cons #\2 1)
; 			     (cons #\c 16))
; 		       *standard-co*
; 		       state
; 		       nil)))
; 	     (change-view (cdr list) (cdr name_var) (cdr type_var) state)))
; 	  (t 

	  (let ((state
	   (fms "~t2 ~x0 ~tc : ~x1"
		(list (cons #\0 (one_element (car name_var)))
		      (cons #\1 (car list))
		      (cons #\2 1)
                      ;(cons #\3 (car type_var))
		      (cons #\c 16))
		  *standard-co*
		  state
		  nil)))
      (change-view (cdr list) (cdr name_var) state))
))

(defun make-func-simul (name-ent name_arch int new_st)
  (let ((name_simul (make-name name-ent name_arch "-simul")))
	`(,name_simul ,int ,new_st)))


; ------ for symbolic simulation --------

(defun make-element (list_of_value i)
  (if (endp list_of_value)
      nil
    `((equal (nth ,i st)
	     ,(car list_of_value))
      ,@(make-element (cdr list_of_value)
		      (1+ i)
		      ))))


(defun make-symsim (name-ent name_arch
		    length_st
		    list_element nb_simul)
  (if (or (zp nb_simul) (= nb_simul 1))
      (let ((name_simul (make-name name-ent name_arch "-simul")))
	`(symsim-for-value (,name_simul 1 st)
		 ((consp st) (integer-listp st) (equal (len st) ,length_st)
		  ,@list_element)
		 :inhibit-output t))
    (let ((name_simul (make-name name-ent name_arch "-simul")))
	`(symsim-for-value (,name_simul ,nb_simul st)
		 ((consp st) (integer-listp st) (equal (len st) ,length_st)
		  ,@list_element)
		 :inhibit-output t))))
	      



(defun affiche_menu (load state)
 (fms "
----------------------------------------------
               ===================
             ((  SIMULATION MENU  ))
               ===================

   1 - Run numeric or symbolic simulation
   2 - Print memory state
   3 - Edit memory state
   4 - Reset memory state

q:return to MAIN MENU  
----------------------------------------------
loaded : ~x0
Vhdl_Acl2> "
(list (cons #\0 load))
   *standard-co* 
   state 
   nil))


(defun symbolic_menu (load state)
 (fms "
----------------------------------------------
               ===================
             ((  SYMBOLIC MENU  ))
               ===================

   1 - Print constraints
   2 - Print Runes
   3 - Remove Runes
             ---
   4 - Prove something

q:return to SIMULATION MENU  
----------------------------------------------
loaded : ~x0
Vhdl_Acl2> "
(list (cons #\0 load))
   *standard-co* 
   state 
   nil))


		  
(defun symb_sim_channel (name-ent arch_name 
			 length_st 
			 list_element
			 nb_simul
			 state)

    (mv-let (a b state) 
		  (ld-fn (list 
		   (cons 'standard-oi 
			 `((in-theory (disable 
				       ; std_logic_vector 
				       logand logxor logior logbit logsetbit lognot
				       binary-logxor binary-logand lognand
				       getarrayi setarrayi
				       b-xor
				       b-not b-nand expt
				       b-and bitp bfix getarrayi setarrayi
				       b-ior
                                       b-nor
				       append
				       binary-+
				       nth update-nth ;nth-update-nth
                                       ))
			   ,(make-symsim name-ent
			     arch_name
			     length_st
			     list_element
			     nb_simul)))
		   (cons 'standard-co "log-output")
		   (cons 'proofs-co "log-proofs")
		   (cons 'ld-error-action :return))
		  state t)
	   (declare (ignore a b))
	   state))

	       
 
 
 (defun welcome (state)
(let ((path (get-global 'connected-book-directory state)))
 (fms "----------------------------------------------
               =============
             ((  MAIN MENU  ))
               =============

     1 - Vhdl -> nif
     2 - nif  -> acl2
     3 - Load a description
                  --
     4 - Change directory path

q:quit           $Date: 2002/05/02 12:29:52 $
----------------------------------------------
~x0
Vhdl_Acl2> "
(list (cons #\0 path))
   *standard-co* 
   state 
   nil)))


(defun list_element_array (i j array)
    (cond ((endp array) nil)
	  (t `((equal (nth ,j (nth ,i st)) ,(car array))
		  ,@(list_element_array i (1+ j) (cdr array))))))
    
(defun list_element_fn (st i lstwc)
    (cond ((endp st) nil)
	  ((consp (car st))
	      (if (< i lstwc)  ;; do not decompose component_state
	            (append (list_element_array i 0 (car st))
			    ;`((equal (nth ,i st) (quote ,(car st))))
		            (list_element_fn (cdr st) (1+ i) lstwc))
	            `((equal (nth ,i st) (quote ,(car st)))
	                ,@(list_element_fn (cdr st) (1+ i) lstwc))))
	  (t `((equal (nth ,i st) ,(car st))
	       ,@(list_element_fn (cdr st) (1+ i) lstwc)))))
     


;;; Change output format of memory state to print friendly


(defun change-output (output state j list_mem_elmt flag)
         
(cond ((and (not (equal output 'ST)) 
	    (or (symbolp output) (acl2-numberp output)))
	   (mv-let (col state)
	          (fmt1 "~% ~t1 ~x0"
		    (list (cons #\0 output) (cons #\1 (+ j 2)))
		     j
		  *standard-co*
		  state
		  nil)
	    (declare (ignore col))
	       state))
	  
       ((endp output) state)
        (t (case-match output
     	

		(('update-nth num rst1 'st)
		    (seq-mv (
			    (state
			     (if flag
				 (fms "~t1 ~x0 :"
				    (list 
				     (cons #\0 (one_element (nth num list_mem_elmt)))  
				     (cons #\1 j))
				    *standard-co*
				    state
				    nil)
				 
				(fms "~t1 ~x0 :"
				    (list 
				     (cons #\0 num)  
				     (cons #\1 j))
				    *standard-co*
				    state
				    nil)))
			    (state
				(change-output rst1 state j list_mem_elmt nil))
			    )
			state))

		  

		(('update-nth num ('update-nth v1 v2 v3) rst2)
		    (seq-mv (
			    (state
				(if flag
				    (fms "~x0 ~% ~t2 ~x1 :"
				    (list (cons #\0 (one_element (nth num list_mem_elmt)))
					  (cons #\1 v1)
					  (cons #\2 j)
					  ;(cons #\3 v2)
					  )
				    *standard-co*
				    state
				    nil)

				    (fms "~x0 ~% ~t2 ~x1 :"
				    (list (cons #\0 num)
					  (cons #\1 v1)
					  (cons #\2 j)
					  ;(cons #\3 v2)
					  )
				    *standard-co*
				    state
				    nil)))
			    (state
				(change-output v2 state (+ j 2) list_mem_elmt nil))
			    (state
				(change-output v3 state j list_mem_elmt nil))
			    (state
				(change-output rst2 state j list_mem_elmt flag)))
			state))
		
		
		
		(('update-nth num rst1 rst2)
		    (seq-mv (
			    (state
			     (if flag
				 (fms "~t1 ~x0 :"
				    (list 
				     (cons #\0 (one_element (nth num list_mem_elmt)))  
				     (cons #\1 j))
				    *standard-co*
				    state
				    nil)
				 
				(fms "~t1 ~x0 :"
				    (list 
				     (cons #\0 num)  
				     (cons #\1 j))
				    *standard-co*
				    state
				    nil)))
			    (state
				(change-output rst1 state j list_mem_elmt nil))
			    (state
				(change-output rst2 state j list_mem_elmt flag)))
			state))


	(('if cond clause-then clause-else)
	    (seq-mv (
		    ((col state)
			(fmt1 "~% ~t0 (if" (list (cons #\0 j))
			    j
			    *standard-co*
			    state
			    nil))
		   (state (change-output cond state (+ 3 j) list_mem_elmt flag))
                   (state (change-output clause-then state (+ 3 j) list_mem_elmt flag))
		   ((col2 state)
		       (fmt1 "~% ~t0 Else "
		             (list (cons #\0 (+ 2 j)))
			     col
		          *standard-co*
		          state
		            nil)
		       (declare (ignore col2)))
		  (state (change-output clause-else state j list_mem_elmt flag))
		  ((col2 state)
		       (fmt1 ")"
		             nil j
		          *standard-co*
		          state
		            nil)
		       (declare (ignore col2))))
		      state))
		

    (('cond . clause-list)
  	(seq-mv (
		 ((col state) (fmt1 "(cond" nil j *standard-co* state nil)
		  (declare (ignore col)))
         	 (state (change-output clause-list state (+ j 3) list_mem_elmt flag))
                 ((col2 state) (fmt1 ") " nil j *standard-co* state nil)
		  (declare (ignore col2))))
		state))
	      
   ((('t ins))
       (seq-mv (
	       ((col state) 
		   (fmt1 "~% ~t0 (t "
		       (list (cons #\0 (+ 2 j)))
		       j
		       *standard-co*
		       state
		       nil)
		   (declare (ignore col)))
	      (state
	       (change-output ins state j list_mem_elmt flag))
	      ((col2 state) 
	       (fmt1 ")"
		    nil
		    j
		    *standard-co*
		    state
		    nil)
	       (declare (ignore col2)))
	      )
	 state))

 
      (('equal var val)
       (seq-mv (
	      ((col state)
		  (fmt1 " (equal "
		      nil
		      j
		      *standard-co*
		      state
		      nil)
		  (declare (ignore col)))
	      (state
	       (change-output var state (+ 3 j) list_mem_elmt flag))
	      (state
	       (change-output val state (+ 3 j) list_mem_elmt flag))
	      ((col state)
		  (fmt1 ")"
		      nil
		      j
		      *standard-co*
		      state
		      nil)
		  (declare (ignore col)))
	      )
	 state))
 
     (
        ((('equal var val) ins) . rst)
       (seq-mv (
	      ((col state)
		  (fmt1 "~% ~t0 (equal ~x1 "
		      (list (cons #\0 (+ 2 j)) (cons #\1 var))
		      j
		      *standard-co*
		      state
		      nil)
		  (declare (ignore col)))
	      (state
	       (change-output val state (+ 3 j) list_mem_elmt flag))
	      (state
	       (change-output ins state (+ 3 j) list_mem_elmt flag))
	      ((col state)
		  (fmt1 ")"
		      nil
		      j
		      *standard-co*
		      state
		      nil)
		  (declare (ignore col)))
	      )
	 (change-output rst state j list_mem_elmt flag)))
	  

      ((fn ('nth i 'st) ('nth k 'st))
	       (mv-let (col state)
		   (fmt1 " (~x1 ~x0 ~x2)"
		     (list (cons #\0 `(nth ,i st))
			   (cons #\1 fn)
			   (cons #\2 `(nth ,k st)))
		     k
		     *standard-co*
		     state
		     nil)
		 (declare (ignore col))
		 state))


      ((fn ('nth i 'st))
	  (mv-let (col state)
	       (fmt1 " (~x1 ~x0)"
		     (list (cons #\0 `(nth ,i st))
			   (cons #\1 fn))
		     j
		     *standard-co*
		     state
		     nil)
	(declare (ignore col))
		 state))

	 
     (('QUOTE val)
	  (change-output val state j list_mem_elmt flag))
            
    
    
	
     ((fn val)
	  (seq-mv (
              ((col state)
		(fmt1 "~% ~t0 (~x1"
		    (list (cons #\0 (+ j 2)) 
			  (cons #\1 fn))
		     j
		     *standard-co*
		     state
		     nil)
		(declare (ignore col)))
	     (state
	       (change-output val state (+ 3 j) list_mem_elmt flag))
             ((col state)
		  (fmt1 ")"
		      nil
		      j
		      *standard-co*
		      state
		      nil)
		  (declare (ignore col))))
	    state))
	  
      ((fn val1 val2)
	  (seq-mv (
              ((col state)
		(fmt1 "~% ~t0 (~x1"
		    (list (cons #\0 (+ 2 j)) 
			  (cons #\1 fn))
		     j
		     *standard-co*
		     state
		     nil)
		(declare (ignore col)))
	     (state
	       (change-output val1 state (+ 3 j) list_mem_elmt flag))
	     (state
	       (change-output val2 state (+ 3 j) list_mem_elmt flag))
             ((col state)
		  (fmt1 ")"
		      nil
		      j
		      *standard-co*
		      state
		      nil)
		  (declare (ignore col))))
	    state))
	 
  
        (& (fms "~t0 ~x1"
		(list (cons #\0 2)
		      (cons #\1 output))
		*standard-co*
		state
		nil)
	
	)))))
;;;

(defun symbolic_choice (name-ent arch_name cons list_element res-untrans state)

   (mv-let (choice state) 
       (read-obj state)
           (case choice
	       
	       (1 ;; Print constraints
		   (seq-mv ((state (fms "Constraints: ~x0"
				   (list (cons #\0 
					   (cadr (get-global 'symsim-for-value-triple state))))
				   *standard-co*
				   state
				   nil))
			   (state (symbolic_menu (concatenate 'string (string name-ent)
				       (string " ")
				       (string arch_name)) state))			 
			   (state (symbolic_choice name-ent arch_name cons list_element res-untrans state)))
		       state))
	       
	       (2 ;; Print Runes
		   (seq-mv ((state (fms "Runes: ~x0"
				   (list (cons #\0 
					   (car (get-global 'symsim-for-value-triple state))))
				   *standard-co*
				   state
				   nil))
			   (state (symbolic_menu (concatenate 'string (string name-ent)
				       (string " ")
				       (string arch_name)) state))			 
			   (state (symbolic_choice name-ent arch_name cons list_element res-untrans state)))
		       state))
	       
	       
	       (3 ;; Remove runes
	          (seq-mv 
		      ((state
			  (fms "Enter rune to remove : "
			      nil
			      *standard-co*
			      state
			      nil))
		      ((rune state)
			  (read-obj state))
		      ((a b state) 
		       (ld `((in-theory (disable ,rune)))
			      :standard-co "log.output")
		       (declare (ignore a b)))
		      (state (symbolic_choice name-ent arch_name cons list_element res-untrans state)))
		   
		   state))
	   
	       (4 ;; prove
	          
		   (seq-mv ((state
			       (fms "Enter memory element to prove (or return): "
				   nil
				   *standard-co*
				   state
				   nil))
			   ((mem-elem state)
			       (read-obj state))
			   (state (if (not mem-elem)
				   ;; if
				   (seq-mv ((state (symbolic_menu (concatenate 'string (string name-ent)
						                            (string " ")
						                            (string arch_name)) state))			 
					   (state (symbolic_choice name-ent arch_name cons list_element res-untrans state)))
				       state)
					   
			           ;; then
				   (seq-mv ((state
					       (fms "Enter expression: "
						   nil
						   *standard-co*
						   state
						   nil))
					   ((expr state)
					       (read-obj state))
					   (desc_acc (make-name name-ent arch_name "-getst"))
					   (new_expr
					       `(implies ,(cons 'and (append list_element (list cons)))
						       (equal (,desc_acc (quote ,mem-elem) ,res-untrans)
							   ,expr)))
					   (state 
(fms "==========================================~%
             THEOREM TO BE PROVEN~%
==========================================
~x0 ~%
*****************************************"
						   (list (cons #\0 (list 'thm new_expr)))
						   *standard-co*
						   state
						   nil))

(state
					       (fms "Do you want to print at screen ? (y or n): "
						   nil
						   *standard-co*
						   state
						   nil))
					   ((dec state)
					       (read-obj state))

                                            ((a b state)
					     (if (equal dec 'y)
						 (thm-fn new_expr state '(("Goal" :in-theory (disable nth update-nth))) nil)
					       (ld `((thm ,new_expr :hints (("Goal" :in-theory (disable nth update-nth)))))
			                          :standard-co "log.output"
						  :proofs-co  "log-proofs")))
					     

					     (state 
					      (if (equal dec 'y)
						  (if (equal a NIL) 
						      (fms "Congratulations ;-) Your property is True."
							   nil
							   *standard-co*
							   state
							   nil)
						    (fms "Sorry, your property cannot be proven"
							 nil
							 *standard-co*
							 state
							 nil))
						(fms "Results are in the file log-proofs"
						     nil
						     *standard-co*
						     state
						     nil))

						)
                                          




                                             ;; debug
			     
			                     ; (state (fms "a: ~x0 b: ~x1"
			                     ;       (list (cons #\0 a)
				       	 ;	         (cons #\1 b))
			                 ;   	*standard-co*
			                 ;    	state
			                 ;    	nil))


					   
                                          )
				        state)))
		          (state (symbolic_menu (concatenate 'string (string name-ent)
				       (string " ")
				       (string arch_name)) state))			 
			   (state (symbolic_choice name-ent arch_name cons list_element res-untrans state)))
		       state))  
	       
	       (t state))))

			       





(mutual-recursion    
 (defun menu2 (list state)

   (mv-let (c state) 
       (read-obj state)
	(case c 
	    
	    (1 (seq-mv ((state
			    (fms "How many simulation cycle : "
				nil
				*standard-co*
				state
				nil))
	    
			((nat state)
			    (read-obj state))
	   
			(name-ent (cadr_assoc_keyword :entity_name list))	    
			(arch_name (cadr_assoc_keyword :architecture_name list)))
            
	     (cond ((symbolicp (@ memory-state))
		 
		     (seq-mv ((state
			    (fms "Enter constraints for symbolic simulation (or return) : "
				nil
				*standard-co*
				state
				nil))
			      (list_mem_elmt
			       (append (cadr_assoc_keyword 
					      :inputs_signals list)
					  (cadr_assoc_keyword 
					      :generic_parameters list)
					  (cadr_assoc_keyword 
					      :local_signals list)
					  (make-next 
                                             (cadr_assoc_keyword 
						:local_signals list))
					  (cadr_assoc_keyword 
					      :local_variables list)
					  (cadr_assoc_keyword 
					      :outputs_signals list)
					  (make-next 
					    (cadr_assoc_keyword 
					        :outputs_signals list))
					  (cadr_assoc_keyword 
					      :list_of_configurations list)))
			     
			     ((cons state)
				 (read-obj state))
			     (len_st_without_config
				 (- (len (@ memory-state))
				    (len (cadr_assoc_keyword :list_of_configurations list))))
			     (list_element (list_element_fn (@ memory-state) 0 len_st_without_config))
			     ;; debug
			     
			     ;(state (fms "list_element: ~x0"
			     ;(list (cons #\0 list_element))
			     ;	*standard-co*
			     ;	state
			     ;	nil))
			     
			     
			      (state (if (equal cons nil)
					 (symb_sim_channel name-ent
				                       arch_name
						       (len (@ memory-state))
						       list_element
						       nat
						       state)
				       (symb_sim_channel name-ent
				                       arch_name
						       (len (@ memory-state))
						       (append list_element (list cons))
						       nat
						       state)))
		              (res (cddr (get-global 'symsim-for-value-triple state)))
			      (res-untrans (untranslate res nil (w state)))
			      

			      (state (fms "Save in file ? (give a name or nil) : "
					  nil
					  *standard-co*
					  state
					  nil))

			      ((file_output state)
			        (read-obj state))

			      (state (if (equal file_output nil)
					 state
				       (write_file file_output
						   res-untrans
						   state)))
			      

			      (state (change-output res-untrans state 
				       1 list_mem_elmt t))

			      (state (symbolic_menu (concatenate 'string (string name-ent)
				                                 (string " ")
						                 (string arch_name)) state))
		              
			    (state (symbolic_choice name-ent arch_name cons list_element res-untrans state))
			    (state (affiche_menu (concatenate 'string (string name-ent)
					(string " ")
					(string arch_name)) state))
			    (state (menu2 list state)))
			state))
  
					
									
		    
	           (t
	   (seq-mv ((value_memory-state (@ memory-state))
		   (new_st (make-func-simul name-ent arch_name
					   nat
					   (list 'quote value_memory-state)))
		   
		   ((e1 value_st state)
                       (my-ev new_st state)
		       (declare (ignore e1)))
		 
		   (state (fms "Save in file ? (give a name or nil) : "
					  nil
					  *standard-co*
					  state
					  nil))

		   ((file_output state)
		    (read-obj state))

		   (state (if (equal file_output nil)
			      state
			    (write_file file_output
					value_st
					state)))
  
		   (state (change-view value_st
			  (append (cadr_assoc_keyword 
					      :inputs_signals list)
					  (cadr_assoc_keyword 
					      :generic_parameters list)
					  (cadr_assoc_keyword 
					      :local_signals list)
					  (make-next 
                                             (cadr_assoc_keyword 
						:local_signals list))
					  (cadr_assoc_keyword 
					      :local_variables list)
					  (cadr_assoc_keyword 
					      :outputs_signals list)
					  (make-next 
					    (cadr_assoc_keyword 
					        :outputs_signals list))
					  (cadr_assoc_keyword 
					      :list_of_configurations list))
			  ; (append (cadr_assoc_keyword :inputs_type list)
; 			  (cadr_assoc_keyword :generic_parameters_type list)
;        			  (cadr_assoc_keyword :local_signals_type list)
;        			  (cadr_assoc_keyword :local_signals_type list)
;        			  (cadr_assoc_keyword :local_variables_type list)			  
;        			  (cadr_assoc_keyword :outputs_type list)
;        			  (cadr_assoc_keyword :outputs_type list))
			   state))
		   
		   ((a b state) (ld `((f-put-global 'memory-state 
				                    (quote ,value_st)
						    state))
				  :standard-co "log-output")
		    (declare (ignore a b)))
		   
	
	      (state (affiche_menu (concatenate 'string (string name-ent)
			                                (string " ")
						        (string arch_name)) state)))
              (menu2 list state))))))

         (2 (seq-mv ((state (fms "Memory state: ~%"
			     nil 
			     *standard-co*
			     state
			     nil))
		     (state (change-view (@ memory-state)
				       (append (cadr_assoc_keyword 
					      :inputs_signals list)
					  (cadr_assoc_keyword 
					      :generic_parameters list)
					  (cadr_assoc_keyword 
					      :local_signals list)
					  (make-next 
                                             (cadr_assoc_keyword 
						:local_signals list))
					  (cadr_assoc_keyword 
					      :local_variables list)
					  (cadr_assoc_keyword 
					      :outputs_signals list)
					  (make-next 
					    (cadr_assoc_keyword 
					        :outputs_signals list))
					  (cadr_assoc_keyword 
					      :list_of_configurations list))
				       ; (append (cadr_assoc_keyword :inputs_type list)
; 			  (cadr_assoc_keyword :generic_parameters_type list)
;        			  (cadr_assoc_keyword :local_signals_type list)
;        			  (cadr_assoc_keyword :local_signals_type list)
;        			  (cadr_assoc_keyword :local_variables_type list)			  
;        			  (cadr_assoc_keyword :outputs_type list)
;        			  (cadr_assoc_keyword :outputs_type list))
				       state))
		     (name-ent (cadr_assoc_keyword :entity_name list))	    
		     (arch_name (cadr_assoc_keyword :architecture_name list))
		     (state (affiche_menu (concatenate 'string (string name-ent)
			                                (string " ")
						        (string arch_name)) state)))
	    (menu2 list state)))
    
    
         (3 (seq-mv ((state (fms! 
"--------------- ~x4 ~x5-----------------
input signals: ~&0
generic parameter: ~&1
local signals: ~&2
variables: ~&3
----------------------------------------
Enter values like :(var1 val1 var2 val2....)
***** For a list or a symbol, use a quote
***** e.g : (a 'a b #b1101 c #b1010)
*****
Modify memory state>"
				     (list (cons #\0 (cadr_assoc_keyword 
						 :inputs_signals list))
					   (cons #\1 (cadr_assoc_keyword 
						 :generic_parameters list))
					   (cons #\2 (cadr_assoc_keyword 
						 :local_signals list))
					   (cons #\3 (cadr_assoc_keyword 
						 :local_variables list))
					   (cons #\4 (cadr_assoc_keyword 
						 :entity_name list))
					   (cons #\5 (cadr_assoc_keyword 
						 :architecture_name list))
				     )
				     *standard-co*
				     state
				     nil))
	           ((s state)
		    (read-obj state))
		
		  (name-ent (cadr_assoc_keyword :entity_name list))	    
		  (arch_name (cadr_assoc_keyword :architecture_name list))
		  (result `(change-state (quote ,name-ent) (quote ,arch_name) (quote ,s) 
					 (quote ,(@ memory-state))))
				 
	          ((e1 value_new_st state)
                       (my-ev result state)
		       (declare (ignore e1)))
				 
                  ((a b state) (ld `((f-put-global 'memory-state 
				                    ,value_new_st
						    state))
				  :standard-co "log.output"))
	          (state (change-view (@ memory-state)
				       (append (cadr_assoc_keyword 
					      :inputs_signals list)
					  (cadr_assoc_keyword 
					      :generic_parameters list)
					  (cadr_assoc_keyword 
					      :local_signals list)
					  (make-next 
                                             (cadr_assoc_keyword 
						:local_signals list))
					  (cadr_assoc_keyword 
					      :local_variables list)
					  (cadr_assoc_keyword 
					      :outputs_signals list)
					  (make-next 
					    (cadr_assoc_keyword 
					        :outputs_signals list))
					  (cadr_assoc_keyword 
					      :list_of_configurations list))

				       ; (append (cadr_assoc_keyword :inputs_type list)
; 			  (cadr_assoc_keyword :generic_parameters_type list)
;        			  (cadr_assoc_keyword :local_signals_type list)
;        			  (cadr_assoc_keyword :local_signals_type list)
;        			  (cadr_assoc_keyword :local_variables_type list)			  
;        			  (cadr_assoc_keyword :outputs_type list)
;        			  (cadr_assoc_keyword :outputs_type list))
				       state))
                    (state (affiche_menu (concatenate 'string (string name-ent)
			                                (string " ")
						        (string arch_name)) state)))
			 
		(menu2 list state)))
			 
	 
	 (4 
	  (seq-mv ((name-ent (cadr_assoc_keyword :entity_name list))	    
		   (arch_name (cadr_assoc_keyword :architecture_name list))
		   (func-make-state (list (make-name name-ent arch_name "-make-state")))
		   ((a b state) (ld `((f-put-global 'memory-state ,func-make-state state)) 
				  :standard-co "log.output")
		    (declare (ignore a b)))
		   (state (affiche_menu (concatenate 'string (string name-ent)
			                                (string " ")
						        (string arch_name)) state)))
	    (menu2 list state)))
	
 	 (q  (let ((state (welcome state)))
	     (menu state)))
    
	 (Newline state)
 	 (t (let ((state 
		   (fms "~% Error : type 1, 2, ..., q.~%Vhdl_Acl2>" 
			      nil
			      *standard-co*
			      state
			      nil)))
	      (menu2 list state))))))


(defun menu (state)
	 	 
 (seq-mv (((c state) (read-obj state)))
	 (case c
	     
	   (1 (seq-mv ((state (fms "Name of vhdl file:"
				     nil
				     *standard-co*
				     state
				     nil))
			 ((s state)
			     (read-obj state))
			 ((status state)
			     (prog2$ (sys-call "v2acl2" `(,(string s)))
				     (sys-call-status state)))		 
			 (state (welcome state)))
			(menu state)))
	     
 	   (2 (seq-mv ((state (fms "Name of .nif file:"
 				     nil
 				     *standard-co*
 				     state
 				     nil))
 			 ((name_file state)
 			     (read-obj state))
 			 ((list state)
 			     (open-in-channel (string-downcase (string name_file)) state))
 			 (state (create-output-files (string-downcase (string name_file))
 						     list 
 						     state))
 			 (state (welcome state)))
 			(menu state)))
		
	   (3 (seq-mv (
                          (state (fms "Choose name :"
 				     nil
 				     *standard-co*
 				     state
 				     nil))
 			 ((s state)
 			    (read-obj state))
			((list state)
			  (open-in-channel (string-downcase (string s)) state)))
                        
                        (if (equal list nil)
                            (let ((state (welcome state)))
                              (menu state))
                          (seq-mv (


			 (state (load-desc-file (string-downcase (string s)) state))
			 (state (affiche_menu 
				      (intern (string s)
					      "ACL2")
				      state))
			  
			  
			  (name-ent (cadr_assoc_keyword :entity_name list))	    
			  (arch_name (cadr_assoc_keyword :architecture_name list))
			  (func-make-state (list (make-name name-ent arch_name "-make-state")))
			  ((a b state) (ld `((f-put-global 'memory-state ,func-make-state state))
					   :standard-co "log.output")
			   (declare (ignore a b))))

			(menu2 list state)))))
	   (4 (seq-mv ((state (fms "~%Give your new path (string):"
				      nil *standard-co* state nil))
			      ((d state) (read-obj state))
			      ((a b state) (ld `((set-cbd ,d)) :standard-co "log.output")
			       (declare (ignore a b)))
			      (state (welcome state)))
			   (menu state)))


	   (q state) ;(exit-to-acl2-shell))
	   (otherwise (seq-mv ((state (fms "~% Error : type 1, 2, ... or q.~%Vhdl_Acl2>" 
					   nil 
					   *standard-co*
					   state
					   nil)))
			      (menu state)))))))
      
      
	   
(defun vhdl-acl2 (state)
   (seq-mv ((state (welcome state))
	    ((c state) (read-obj state))
	   )
	  (case c
	        (1 (seq-mv ((state (fms "Name of entity:"
				     nil
				     *standard-co*
				     state
				     nil))
			 ((s state)
			     (read-obj state))
                         (state (fms "Name of architecture:"
				     nil
				     *standard-co*
				     state
				     nil))
			 ((s2 state)
			     (read-obj state))
			 
			 (state (fms "Name of output file :"
				     nil
				     *standard-co*
				     state
				     nil))
			 ((out state)
			     (read-obj state))

			 ((status state)
			     (prog2$ (sys-call "v2acl2" '("-e" s "-a" s2 "-o" out))
				     (sys-call-status state))
			     (declare (ignore status)))
			 
			 (state (welcome state)))
			(menu state)))
		(2 (seq-mv ((state (fms "Name of .nif file:"
				     nil
				     *standard-co*
				     state
				     nil))
			 ((s state)
			     (read-obj state))
			 ((list state)
			     (open-in-channel (string-downcase (string s))
				              state))
			 (state (create-output-files (string-downcase (string s))
						     list 
						     state))
			 (state (welcome state)))
			(menu state)))

	   (3 (seq-mv (
                          (state (fms "Choose name :"
 				     nil
 				     *standard-co*
 				     state
 				     nil))
 			 ((s state)
 			    (read-obj state))
			((list state)
			  (open-in-channel (string-downcase (string s)) state)))
                        
                        (if (equal list nil)
                            (let ((state (welcome state)))
                            (menu state))
                          (seq-mv (


			 (state (load-desc-file (string-downcase (string s)) state))
			 (state (affiche_menu 
				      (intern (string s)
					      "ACL2")
				      state))
			  
			  
			  (name-ent (cadr_assoc_keyword :entity_name list))	    
			  (arch_name (cadr_assoc_keyword :architecture_name list))
			  (func-make-state (list (make-name name-ent arch_name "-make-state")))
			  ((a b state) (ld `((f-put-global 'memory-state ,func-make-state state))
					   :standard-co "log.output")
			   (declare (ignore a b))))

			(menu2 list state)))))

		(4 (seq-mv ((state (fms "~%Give your new absolute path (string):"
				      nil *standard-co* state nil))
			      ((d state) (read-obj state))		      
			      ((a b state) (ld `((set-cbd ,d)) :standard-co "log.output")
			        (declare (ignore a b)))
			      (state (welcome state)))
			   (menu state)))
		(Newline state)
		(q state) ; exit to acl2
		(t (seq-mv ((state (fms 
				    "~% Error : type 1, 2, ... or q.~%Vhdl_Acl2> " 
				    nil 
				    *standard-co*
				    state
				    nil)))
			   (menu state))))))

       
(defmacro v2acl2 ()
    `(vhdl-acl2 state))

(logic)
:comp t
