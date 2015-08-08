(in-package "ACL2")
(include-book "../../../../arithmetic/top")
(include-book "../../../../ihs/ihs-definitions")
(include-book "../../../../ihs/ihs-lemmas")
(include-book "../../../../misc/expander")
(defconst *nif2acl2_directory* "/users/gp34/nif2acl2")
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; File utils.lisp  for vhdl-acl2
;
;   Written by : Philippe Georgelin                                        ;
;   Email : Philippe.Georgelin@st.com
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(local
 (in-theory (disable functional-commutativity-of-minus-*-left
                    ; rearrange-negative-coefs-equal
)))

(defun make-name (prefix name suffix)
    (intern (string-upcase (concatenate 'string (string prefix)
					 (string name)
					 (string suffix)))
	    "ACL2"))



(defun digit-to-string (n)
  (if (and (<= 0 n) (< n 10))
      (nth n '("0" "1" "2" "3" "4" "5" "6" "7" "8" "9"))
      "*"))

(defun natural-to-string (arg)
  (let* ((n (nfix arg))
	 (quot (nonnegative-integer-quotient n 10))
	 (rest (- n (* quot 10))))
    (if (< n 10)
	(digit-to-string n)
        (concatenate 'string (natural-to-string quot)
		             (digit-to-string rest)))))

;; Explore chaque expression en partie droite
(defun explore_right_expr (expr)
  (cond ((symbolp expr)
	 ;(if (consp (member expr list_of_left_elmt))
	     (list expr))
	  ; nil))

;; unary operation
	((and (consp expr)
	      (equal (len expr) 2))
	 (explore_right_expr (cadr expr)))

;;  index
	((and (consp expr)
	      (equal (car expr) 'index))
	 (list (make-name (string (cadr expr))
			  (natural-to-string (- (cadr (nth 2 expr))
				     (caddr (nth 2 expr))))
			  "")))

;; binary operation
	((and (consp expr)
	      (equal (len expr) 3))
	 (append (explore_right_expr (cadr expr))
		 (explore_right_expr (caddr expr))))))


;ACL2 !>(explore_right_expr '(NOT (OR (OR I3 I4) A)))
;(i3 i4 a)


(defun explore_one_conc_instr (list_of_conc_inst i list_accu)
  (cond ((endp list_of_conc_inst)
	 list_accu)
	(t
  (let ((res_exp (explore_right_expr (nth 2 (car list_of_conc_inst))))
	(left_elmt (if (symbolp (caar list_of_conc_inst))
		       (caar list_of_conc_inst)
		     (let ((expr (caar list_of_conc_inst)))
		       (make-name (string (cadr expr))
				  (natural-to-string (- (cadr (nth 2 expr))
							(caddr (nth 2 expr))))
				"")))))
    (if (consp res_exp)
	(explore_one_conc_instr (cdr list_of_conc_inst) (1+ i)
		   (update-nth i
			       (list left_elmt res_exp)
			       list_accu))
      (explore_one_conc_instr (cdr list_of_conc_inst) (1+ i)
			      (update-nth i
					  (list (nth i list_accu))
					  list_accu)
		    ))))))


#|
ACL2 !>(explore_one_conc_instr '(   (SNOT <= (NOT B))
   (I1 <= (AND (AND B (index S (- 3 3))) A))
   (I2 <= (AND (AND A (index S (- 3 2))) SNOT))
   (I3 <= (AND SNOT (index S (- 3 1))))
   (I4 <= (AND (index S (- 3 0)) B))
   (XINT <= (NOR I1 I2))
   (YINT <= (NOT (OR (OR I3 I4) A)))
  ) 0 nil)

((snot (b))
 (i1 (b s0 a))
 (i2 (a s1 snot))
 (i3 (snot s2))
 (i4 (s3 b))
 (xint (i1 i2))
 (yint (i3 i4 a)))

|#


(defun update_list (elmt new list)
  (cond ((endp list) list)
	(t (if (equal elmt (car list))
	       (cons new (cdr list))
	     (cons (car list) (update_list elmt new (cdr list)))))))

(defun search_dep (elmt dep)
  (cond ((endp dep) nil)
	(t (if (equal elmt (caar dep))
	       (cadar dep)
	     (search_dep elmt (cdr dep))))))


(defun replace_in_dep (right_list dep)
  (cond ((endp right_list) nil)
	(t (let* ((first_element (car right_list))
		 (search_dep_res (search_dep first_element dep)))
	     (if (equal search_dep_res nil)
		 (cons first_element (replace_in_dep (cdr right_list) dep))
	      (cons (update_list first_element
			    search_dep_res
			    right_list)
		    (replace_in_dep (cdr right_list) dep)))))))


#|

ACL2 !>(replace_in_dep '(i1 i2 b) '((snot (b))
 (i1 (b s a))
 (i2 (a s snot))
 (i3 (snot s))
 (i4 (s b))
 (xint (i1 i2))
 (yint (i3 i4 a))))
(((b s a) i2 b) ((a s snot) b) b)
|#


(defun all_dep (dep dep_orig)
  (cond ((endp dep) nil)
	(t (let* ((car_dep (car dep))
		  (expr (cadr car_dep))
		  (replace_new (replace_in_dep expr dep_orig)))
	     (cons (cons (car car_dep) (list replace_new)) (all_dep (cdr dep) dep_orig))))))



(defun rec_all_dep (dep i)
  (cond ((zp i) dep)
	(t (rec_all_dep
	    (all_dep dep dep)
	    (1- i)))))



#|
ACL2 !>(all_dep '((snot (b))
 (i1 (b s a))
 (i2 (a s snot))
 (i3 (snot s))
 (i4 (s b))
 (xint (i1 i2))
 (yint (i3 i4 a))) '((snot (b))
 (i1 (b s a))
 (i2 (a s snot))
 (i3 (snot s))
 (i4 (s b))
 (xint (i1 i2))
 (yint (i3 i4 a))))

((snot (b))
 (i1 (b s a))
 (i2 (a s ((b))))
 (i3 (((b) s) s))
 (i4 (s b))
 (xint (((b s a) i2) ((a s snot))))
 (yint (((snot s) i4 a) ((s b) a) a)))

|#

(defun profondeur_noeud (node accu accu_max)
  (cond ((symbolp node) (if (> accu accu_max)
			    accu
			  accu_max))
	((endp node) (if (> accu accu_max)
			 accu
		       accu_max))
	(t (let ((car_node (car node)))
	     (if (consp car_node)
		 (let ((prof_res (profondeur_noeud car_node (1+ accu) accu_max)))
		   (if (< accu_max prof_res)
		       (profondeur_noeud (cdr node) accu prof_res)
		     (profondeur_noeud (cdr node) accu accu_max)))
	       (profondeur_noeud (cdr node) accu accu_max))))))

#|
ACL2 !>(profondeur_noeud '(((b s a) i2) ((a s snot))) 0 0)
2
ACL2 !>(profondeur_noeud '(((b) s) s) 0 0)
2
ACL2 !>(profondeur_noeud '(a s ((b))) 0 0)
2
ACL2 !>(profondeur_noeud '(b s a) 0 0)
0
|#

(defun profondeur (dep accu)
  (cond ((endp dep) accu)
	(t (let ((prof (profondeur_noeud (cadar dep) 0 0)))
	     (if (> prof accu)
		 (profondeur (cdr dep) prof)
	       (profondeur (cdr dep) accu))))))

#|

ACL2 !>(profondeur '((snot (b))
 (i1 (b s a))
 (i2 (a s ((b))))
 (i3 (((b) s) s))
 (i4 (s b))
 (xint (((b s a) i2) ((a s snot))))
 (yint (((snot s) i4 a) ((s b) a) a))) 0)
2

|#




;; some recognizer predicate
(defmacro std_logicp (x)
  `(bitp ,x))

(defmacro std_logic_vectorp (x)
  `(integerp ,x))

(defmacro signedp (x)
  `(integerp ,x))

(defmacro bitvecp (x)
  `(naturalp ,x))

(defmacro positivep (x)
  `(and (integerp ,x) (>= ,x 1)))

(defun array-bitp1 (X N)
  (declare (type integer N))
  (if (consp X)
     (if (equal (CAR X) '1)
         (array-bitp1 (CDR X) (1- N))
         (if (equal (CAR X) '0)
             (array-bitp1 (CDR X) (1- N))
             'nil))
     (if (equal X 'nil)
	    (equal N '0)
            'nil)))


(defmacro array-bitp (x)
  `(array-bitp1 ,x (length ,x)))

(defmacro array-std_logicp (x)
  `(array-bitp1 ,x (length ,x)))

(defmacro naturalp (n)
    `(and (integerp ,n) (>= ,n 0)))


(defmacro unsignedp (x)
  `(naturalp ,x))

(defun binding? (x)
  (declare (xargs :guard t))
  (or (null x)
      (and (consp x)
           (true-listp (car x))
           (or (symbolp (caar x))
               (and (symbol-listp (caar x))
                    (consp (caar x))))
           (binding? (cdr x)))))


(defun seq-fn+ (bind result)
  (declare (xargs :guard (binding? bind)))
  (cond ((endp bind) result)
        ((atom (caar bind))
         `(let ((,(caar bind)
                 ,(cadar bind)))
            ,(seq-fn+ (cdr bind) result)))
        ((endp (cdaar bind))
         `(let ((,(caaar bind)
                 ,(cadar bind)))
            ,(seq-fn+ (cdr bind) result)))
        (t
         (if (equal (caddar bind) nil)
	     `(mv-let ,(caar bind)
		      ,(cadar bind)
		      ,(seq-fn+ (cdr bind) result))
	    `(mv-let ,(caar bind)
		      ,(cadar bind)
		      ,(caddar bind)
		      ,(seq-fn+ (cdr bind) result))))))


(defmacro seq-mv (bind result)
  (declare (xargs :guard (binding? bind)))
  (seq-fn+ bind result))



(defmacro seq (mem &rest rst)
   (cond ((endp rst) mem)
         ((endp (cdr rst)) (car rst))
         (t `(let ((,mem ,(car rst)))
              (seq ,mem ,@(cdr rst))))))


(defun make-onename (name)
    (intern (string-upcase (string name))
	    "ACL2"))


(defun key-list-make (list_inputs
		      list_value)
  (if (endp list_inputs)
      nil
    `(,(intern (string (car list_inputs))
	       "ACL2")
      ,(car list_value)
      ,@(key-list-make (cdr list_inputs)
		       (cdr list_value)))))



(defmacro cadr_assoc_keyword (x l)
  `(cadr (assoc-keyword ,x ,l)))


(defun logsetbit (i new int)
  (cond ((zp i)
	 (logcons new (logcdr int)))
	(t
	 (logcons (logcar int)
		  (logsetbit (1- i) new (logcdr int))))))



(defun setarrayi (key new list)
  (cond ((true-listp list)
	(update-nth key new list))
	((integerp list)
	 (logsetbit key new list))))

(defun getarrayi (list i)
  (cond ((true-listp list)
           (nth i list))
	((integerp list)
	 (logbit i list))))

(defmacro defarray (size &key (initial-element '0))
  `(make-list ,size :initial-element ,initial-element))


(defun change-state (name-ent name_arch key-list-arg st)
  (if (endp key-list-arg)
      nil
    (let ((key (car key-list-arg))
	  (dest (cadr key-list-arg)))
      (if (equal (cddr key-list-arg)
		 nil)

	    `(,(make-name name-ent
			    name_arch
			    "-putst")
	      (quote ,(make-name ""
			       (string key)
			       ""))
		      ,dest
		       (quote ,st))


    `(,(make-name name-ent name_arch "-putst")
      (quote ,(make-name ""
			       (string key)
			       ""))
	    ,dest
	    ,(change-state
	      name-ent
	      name_arch
	       (cddr key-list-arg)
	       st))))))



(defun update-state-body (name-ent name_arch key-list-arg st)
  (if (endp key-list-arg)
      nil
    (let ((key (car key-list-arg))
	  (dest (cadr key-list-arg)))
      (if (equal (cddr key-list-arg)
		 nil)
	  (if (symbolp dest)
	      `(,(make-name name-ent
			    name_arch
			    "-putst")
		(quote ,(make-name ""
			       (string key)
			       ""))
		      (,(make-name name-ent
				   name_arch
				   "-getst")
		       (quote ,dest)
			     ,st)
		      ,st)

	    `(,(make-name name-ent
			    name_arch
			    "-putst")
	      (quote ,(make-name ""
			       (string key)
			       ""))
		      ,dest
		       (quote ,st)))

	(if (symbolp dest)

    `(,(make-name name-ent
			    name_arch
			    "-putst")
      (quote ,(make-name ""
			       (string key)
			       ""))
	    (,(make-name name-ent
				   name_arch
				   "-getst")
	     (quote ,dest)
		   ,st)
	    ,(update-state-body
	      name-ent
	      name_arch
	       (cddr key-list-arg)
	       st))

    `(,(make-name name-ent
			    name_arch
			    "-putst")
      (quote ,(make-name ""
			       (string key)
			       ""))
	    ,dest
	    ,(update-state-body
	      name-ent
	      name_arch
	       (cddr key-list-arg)
	       st)))))))




(defun app2-fn (final_vec vec i j)
  (if (zp i)
      (setarrayi
       j
       (getarrayi vec i)
       final_vec)
    (let ((new_veci (setarrayi
		     (+ i j)
		     (getarrayi vec i)
		     final_vec)))
      (app2-fn new_veci
	    vec
	    (1- i)
	    j))))


(defun app-fn (vec list i)
  (if (endp list)
      vec
    (let* ((first_list (car list))
           (rest_list (cdr list))
	   (len_car (len first_list))
	   (new_vec (app2-fn vec first_list (1- len_car) i)))
            (app-fn
	        new_vec
	        rest_list
	        (+ i len_car)))))

(defun total_length (list)
  (if (endp list)
      0
    (+ (len (car list))
       (total_length (cdr list)))))

#|

(defun std_logic_vector-fn-unsigned (int result i)
  (if (and (naturalp int) (naturalp i))
      (if (or (= int 0) (>= i (len result)))
	  result
	(if (= (mod int 2) 0)
	    (std_logic_vector-fn-unsigned
	     (NONNEGATIVE-INTEGER-QUOTIENT int 2)
	     (setarrayi i
			0
			result)
	     (1+ i)
	     )
	  (std_logic_vector-fn-unsigned
	   (NONNEGATIVE-INTEGER-QUOTIENT int 2)
	   (setarrayi i
		      1
		      result)
	     (1+ i)
	   )))
	nil))


(defthm lemma_std_unsigned
  (implies (true-listp result)
	   (true-listp (std_logic_vector-fn-unsigned int
						     result
						     i))))


(defun complete_by_1 (result i size)
  (declare (xargs :measure (nfix (- size i))))
  (if (and (naturalp i) (naturalp size))
      (if (= (nfix (- size i))
	     0)
	  result
	(complete_by_1
	 (setarrayi i 1 result)
	 (1+ i)
	 size))
    (cw "Error : i or size not integer")))


(defthm true-listp-complete_by_1
  (implies (true-listp result)
	   (true-listp (complete_by_1 result i size))))


(defthm length_of_complete_by_1
  (implies (and (naturalp i)
		(naturalp size)
		(< size (len result)))
	   (equal (len (complete_by_1 result i size))
		  (len result))))


(defun std_logic_vector-fn-signed (int result i size)
  (if (and (naturalp int) (naturalp i))
      (if (or (= int 0) (>= i (len result)))
	  (complete_by_1 result (1+ i) size)

	(if (= (mod int 2) 0)
	    (std_logic_vector-fn-signed
	     (NONNEGATIVE-INTEGER-QUOTIENT int 2)
	     (setarrayi i
			1
			result)
	     (1+ i)
	     size
	     )
	  (std_logic_vector-fn-signed
	   (NONNEGATIVE-INTEGER-QUOTIENT int 2)
	   (setarrayi i
		      0
		      result)
	   (1+ i)
	   size)))
	nil))


(defthm lemma_std_signed
  (implies (true-listp result)
	   (true-listp (std_logic_vector-fn-signed int
						   result
						   i
						   size))))


(defun std_logic_vector (int size)
  (if (and (integerp int) (naturalp size))
      (let ((result (defarray size :initial-element 0)))
      (if (< int 0)
	  (std_logic_vector-fn-signed (- (1+ int)) result 0 size)
	  (std_logic_vector-fn-unsigned int result 0)))
    (cw "Error on std_logic_vector : not an integer")))



(defthm consp_make-list-ac
  (implies (and (naturalp size)
		(< 0 size))
	   (consp (make-list-ac size 0 nil))))

; Q.E.D


  (MAKE-LIST-AC SIZE 0 NIL)

(defthm unary--lemma
  (implies (and (integerp int)
		(< int 0))
	   (and (integerp (+ -1 (- INT)))
		(<= 0 (+ -1 (- INT))))))

; Q.E.D

;; length of std_logic_vector is size
(defthm length_std_logic_vector
  (implies (and (integerp int)
		(naturalp size)
		(< 0 size))
		(equal (len (std_logic_vector int size))
		       size)))



;; std_logic_vector -> unsigned
(defun unsigned (vec size i)
  (declare (xargs :measure (nfix (- size i))))
  (if (and (naturalp size) (naturalp i)
	   (>= size i))
      (if (= size i)
	  0
    (case (getarrayi vec i)
	  (1 (logcons 1 (unsigned vec size (1+ i))))
	  (0 (logcons 0 (unsigned vec size (1+ i))))))
     (cw "Error on unsigned : size and i must be natural")))



(defun vec{1+} (vec ret size i)
  (declare (xargs :measure (nfix (- size i))))
  (if (and (naturalp size) (naturalp i)
	   (>= size i))
      (if (= size i)
	  vec
	(case ret
	  (0 (vec{1+} vec ret size (1+ i)))
	  (1 (case (getarrayi vec i)
		(0 (vec{1+} (setarrayi i 1 vec) 0 size (1+ i)))
		(1 (vec{1+} (setarrayi i 0 vec) 1 size (1+ i)))
		(otherwise
		 (cw "Error : not an bit-vector "))))
	  (otherwise
	   (cw "Error : ret must be 1 or 0"))))
    (cw "Error on vec{1+} : size and i must be natural")))



(defun vec{not} (vec size i)
  (declare (xargs :measure (nfix (- size i))))
  (if (and (naturalp size) (naturalp i)
	   (>= size i))
      (if (= size i)
	  vec
	(case (getarrayi vec i)
	      (1 (vec{not} (setarrayi i 0 vec) size (1+ i)))
	      (0 (vec{not} (setarrayi i 1 vec) size (1+ i)))
	      (otherwise (cw "Error on vec{not} : not an bit-vector "))))
    (cw "Error in vec{not} : not integer ")))


(defun signed (vec size)
      (if (equal (getarrayi vec (1- size))
		 0)
	  (unsigned vec size 0)
	(- (unsigned
           (vec{1+} (vec{not} vec size 0) 1 size 0) size 0))))


|#

(defun other-fn (vec i size number)
  (declare (xargs :measure (nfix (- size i))))
  (if (and (naturalp size) (naturalp i)
	   (>= size i))
      (if (= size i)
	  vec
	  (if (consp (member i number))
	      (other-fn
	       (setarrayi i 1 vec)
	       (1+ i)
	       size
	       number)
	    (other-fn
	      (setarrayi i 0 vec)
	      (1+ i)
	      size
	      number)))
    (cw "Error on args of other : size and i")))


(defmacro others (size &rest number)
     `(other-fn (defarray ,size :initial-element '0)
		0
	       ,size
	       (quote ,number)))

(defmacro new (size &rest number)
  `(others ,size ,@number))


(defabbrev $if (a b c)
  (if a b c))

(defthm lemma_nth_update-nth1
    (implies (not (equal (nfix n) (nfix m)))
             (equal (nth n (update-nth m val st))
                    (nth n st))))


(defthm lemma_nth_update-nth2bis
    (implies (and (integerp n) (<= 0 n))
             (equal (nth n (update-nth n val st))
                    val)))



(defthm lemma_nth_update-nth3
    (equal (update-nth n v1 (update-nth n v2 st))
           (update-nth n v1 st)))


(defthm update-nth-diff
    (implies
       (not (equal (nfix i1) (nfix i2)))
       (equal (update-nth i1 v1 (update-nth i2 v2 st))
              (update-nth i2 v2 (update-nth i1 v1 st))))
     :rule-classes ((:rewrite :loop-stopper ((i1 i2)))))



(defthm >_not_equal
      (implies (and (integerp q) (> q 1))
              (and (equal (equal q 1) nil)
                   (equal (equal q 0) nil))))



(defthm b-not_b-not
    (implies (bitp a)
	(equal (b-not (b-not a))
		a)))
