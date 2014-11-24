; XDOC Documentation System for ACL2
; Copyright (C) 2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@centtech.com>
; with contributions from Matt Kaufmann

; Emacs tool in support of defdoc -> defxdoc converter

; I ran the following events in ACL2 and got the alist noted below.

; ACL2 !>(defun doc-underscore-table-1 (syms acc)
;   (declare (xargs :mode :program))
;   (cond ((endp syms) acc)
;         (t (doc-underscore-table-1
;             (cdr syms)
;             (let ((str (and (symbolp (car syms))
;                             (symbol-name (car syms)))))
;               (cond ((null str)
;                      acc)
;                     ((position #\Space str)
;                      (cons (cons (concatenate 'string
;                                               "|"
;                                               str
;                                               "|")
;                                  
;                                  (concatenate 'string
;                                               "|"
;                                               (substitute #\_
;                                                           #\Space
;                                                           str)
;                                               "|"))
;                            acc))
;                     (t acc)))))))
; 
; Summary
; Form:  ( DEFUN DOC-UNDERSCORE-TABLE-1 ...)
; Rules: NIL
; Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)
;  DOC-UNDERSCORE-TABLE-1
; ACL2 !>(defun doc-underscore-table (state)
;   (declare (xargs :stobjs state :mode :program))
;   (doc-underscore-table-1
;    (strip-cars (global-val 'documentation-alist (w state)))
;    nil))
; 
; Summary
; Form:  ( DEFUN DOC-UNDERSCORE-TABLE ...)
; Rules: NIL
; Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)
;  DOC-UNDERSCORE-TABLE
; ACL2 !>(DOC-UNDERSCORE-TABLE state)

(defvar *doc-fix-alist*
  '(("|You Must Think about the Use of a Formula as a Rule|"
     .
     "|You_Must_Think_about_the_Use_of_a_Formula_as_a_Rule|")
    ("|What is a Mechanical Theorem Prover(Q) (cont)|"
     .
     "|What_is_a_Mechanical_Theorem_Prover(Q)_(cont)|")
    ("|What is a Mechanical Theorem Prover(Q)|"
     .
     "|What_is_a_Mechanical_Theorem_Prover(Q)|")
    ("|What is a Mathematical Logic(Q)|" . "|What_is_a_Mathematical_Logic(Q)|")
    ("|What is Required of the User(Q)|" . "|What_is_Required_of_the_User(Q)|")
    ("|What Is ACL2(Q)|" . "|What_Is_ACL2(Q)|")
    ("|Using the Associativity of App to Prove a Trivial Consequence|"
     .
     "|Using_the_Associativity_of_App_to_Prove_a_Trivial_Consequence|")
    ("|Undocumented Topic|" . "|Undocumented_Topic|")
    ("|The WARNING about the Trivial Consequence|"
     .
     "|The_WARNING_about_the_Trivial_Consequence|")
    ("|The Tours|" . "|The_Tours|")
    ("|The Time Taken to do the Associativity of App Proof|"
     .
     "|The_Time_Taken_to_do_the_Associativity_of_App_Proof|")
    ("|The Theorem that App is Associative|"
     .
     "|The_Theorem_that_App_is_Associative|")
    ("|The Summary of the Proof of the Trivial Consequence|"
     .
     "|The_Summary_of_the_Proof_of_the_Trivial_Consequence|")
    ("|The Simplification of the Induction Conclusion (Step 9)|"
     .
     "|The_Simplification_of_the_Induction_Conclusion_(Step_9)|")
    ("|The Simplification of the Induction Conclusion (Step 8)|"
     .
     "|The_Simplification_of_the_Induction_Conclusion_(Step_8)|")
    ("|The Simplification of the Induction Conclusion (Step 7)|"
     .
     "|The_Simplification_of_the_Induction_Conclusion_(Step_7)|")
    ("|The Simplification of the Induction Conclusion (Step 6)|"
     .
     "|The_Simplification_of_the_Induction_Conclusion_(Step_6)|")
    ("|The Simplification of the Induction Conclusion (Step 5)|"
     .
     "|The_Simplification_of_the_Induction_Conclusion_(Step_5)|")
    ("|The Simplification of the Induction Conclusion (Step 4)|"
     .
     "|The_Simplification_of_the_Induction_Conclusion_(Step_4)|")
    ("|The Simplification of the Induction Conclusion (Step 3)|"
     .
     "|The_Simplification_of_the_Induction_Conclusion_(Step_3)|")
    ("|The Simplification of the Induction Conclusion (Step 2)|"
     .
     "|The_Simplification_of_the_Induction_Conclusion_(Step_2)|")
    ("|The Simplification of the Induction Conclusion (Step 12)|"
     .
     "|The_Simplification_of_the_Induction_Conclusion_(Step_12)|")
    ("|The Simplification of the Induction Conclusion (Step 11)|"
     .
     "|The_Simplification_of_the_Induction_Conclusion_(Step_11)|")
    ("|The Simplification of the Induction Conclusion (Step 10)|"
     .
     "|The_Simplification_of_the_Induction_Conclusion_(Step_10)|")
    ("|The Simplification of the Induction Conclusion (Step 1)|"
     .
     "|The_Simplification_of_the_Induction_Conclusion_(Step_1)|")
    ("|The Simplification of the Induction Conclusion (Step 0)|"
     .
     "|The_Simplification_of_the_Induction_Conclusion_(Step_0)|")
    ("|The Rules used in the Associativity of App Proof|"
     .
     "|The_Rules_used_in_the_Associativity_of_App_Proof|")
    ("|The Q.E.D. Message|" . "|The_Q.E.D._Message|")
    ("|The Proof of the Associativity of App|"
     .
     "|The_Proof_of_the_Associativity_of_App|")
    ("|The Justification of the Induction Scheme|"
     .
     "|The_Justification_of_the_Induction_Scheme|")
    ("|The Instantiation of the Induction Scheme|"
     .
     "|The_Instantiation_of_the_Induction_Scheme|")
    ("|The Induction Step in the App Example|"
     .
     "|The_Induction_Step_in_the_App_Example|")
    ("|The Induction Scheme Selected for the App Example|"
     .
     "|The_Induction_Scheme_Selected_for_the_App_Example|")
    ("|The First Application of the Associativity Rule|"
     .
     "|The_First_Application_of_the_Associativity_Rule|")
    ("|The Final Simplification in the Base Case (Step 3)|"
     .
     "|The_Final_Simplification_in_the_Base_Case_(Step_3)|")
    ("|The Final Simplification in the Base Case (Step 2)|"
     .
     "|The_Final_Simplification_in_the_Base_Case_(Step_2)|")
    ("|The Final Simplification in the Base Case (Step 1)|"
     .
     "|The_Final_Simplification_in_the_Base_Case_(Step_1)|")
    ("|The Final Simplification in the Base Case (Step 0)|"
     .
     "|The_Final_Simplification_in_the_Base_Case_(Step_0)|")
    ("|The Falling Body Model|" . "|The_Falling_Body_Model|")
    ("|The Expansion of ENDP in the Induction Step (Step 2)|"
     .
     "|The_Expansion_of_ENDP_in_the_Induction_Step_(Step_2)|")
    ("|The Expansion of ENDP in the Induction Step (Step 1)|"
     .
     "|The_Expansion_of_ENDP_in_the_Induction_Step_(Step_1)|")
    ("|The Expansion of ENDP in the Induction Step (Step 0)|"
     .
     "|The_Expansion_of_ENDP_in_the_Induction_Step_(Step_0)|")
    ("|The Event Summary|" . "|The_Event_Summary|")
    ("|The End of the Walking Tour|" . "|The_End_of_the_Walking_Tour|")
    ("|The End of the Proof of the Associativity of App|"
     .
     "|The_End_of_the_Proof_of_the_Associativity_of_App|")
    ("|The End of the Flying Tour|" . "|The_End_of_the_Flying_Tour|")
    ("|The Base Case in the App Example|"
     . "|The_Base_Case_in_the_App_Example|")
    ("|The Associativity of App|" . "|The_Associativity_of_App|")
    ("|The Admission of App|" . "|The_Admission_of_App|")
    ("|Symbolic Execution of Models|" . "|Symbolic_Execution_of_Models|")
    ("|Suggested Inductions in the Associativity of App Example|"
     .
     "|Suggested_Inductions_in_the_Associativity_of_App_Example|")
    ("|Subsumption of Induction Candidates in App Example|"
     .
     "|Subsumption_of_Induction_Candidates_in_App_Example|")
    ("|Running Models|" . "|Running_Models|")
    ("|Rewrite Rules are Generated from DEFTHM Events|"
     .
     "|Rewrite_Rules_are_Generated_from_DEFTHM_Events|")
    ("|Revisiting the Admission of App|" . "|Revisiting_the_Admission_of_App|")
    ("|Proving Theorems about Models|" . "|Proving_Theorems_about_Models|")
    ("|Popping out of an Inductive Proof|"
     . "|Popping_out_of_an_Inductive_Proof|")
    ("|Pages Written Especially for the Tours|"
     .
     "|Pages_Written_Especially_for_the_Tours|")
    ("|Overview of the Simplification of the Induction Step to T|"
     .
     "|Overview_of_the_Simplification_of_the_Induction_Step_to_T|")
    ("|Overview of the Simplification of the Induction Conclusion|"
     .
     "|Overview_of_the_Simplification_of_the_Induction_Conclusion|")
    ("|Overview of the Simplification of the Base Case to T|"
     .
     "|Overview_of_the_Simplification_of_the_Base_Case_to_T|")
    ("|Overview of the Proof of a Trivial Consequence|"
     .
     "|Overview_of_the_Proof_of_a_Trivial_Consequence|")
    ("|Overview of the Final Simplification in the Base Case|"
     .
     "|Overview_of_the_Final_Simplification_in_the_Base_Case|")
    ("|Overview of the Expansion of ENDP in the Induction Step|"
     .
     "|Overview_of_the_Expansion_of_ENDP_in_the_Induction_Step|")
    ("|Overview of the Expansion of ENDP in the Base Case|"
     .
     "|Overview_of_the_Expansion_of_ENDP_in_the_Base_Case|")
    ("|Other Requirements|" . "|Other_Requirements|")
    ("|On the Naming of Subgoals|" . "|On_the_Naming_of_Subgoals|")
    ("|Numbers in ACL2|" . "|Numbers_in_ACL2|")
    ("|Nontautological Subgoals|" . "|Nontautological_Subgoals|")
    ("|Name the Formula Above|" . "|Name_the_Formula_Above|")
    ("|Models of Computer Hardware and Software|"
     .
     "|Models_of_Computer_Hardware_and_Software|")
    ("|Models in Engineering|" . "|Models_in_Engineering|")
    ("|Modeling in ACL2|" . "|Modeling_in_ACL2|")
    ("|How To Find Out about ACL2 Functions (cont)|"
     .
     "|How_To_Find_Out_about_ACL2_Functions_(cont)|")
    ("|How To Find Out about ACL2 Functions|"
     .
     "|How_To_Find_Out_about_ACL2_Functions|")
    ("|How Long Does It Take to Become an Effective User(Q)|"
     .
     "|How_Long_Does_It_Take_to_Become_an_Effective_User(Q)|")
    ("|Hey Wait!  Is ACL2 Typed or Untyped(Q)|"
     .
     "|Hey_Wait!__Is_ACL2_Typed_or_Untyped(Q)|")
    ("|Guiding the ACL2 Theorem Prover|" . "|Guiding_the_ACL2_Theorem_Prover|")
    ("|Guessing the Type of a Newly Admitted Function|"
     .
     "|Guessing_the_Type_of_a_Newly_Admitted_Function|")
    ("|Functions for Manipulating these Objects|"
     .
     "|Functions_for_Manipulating_these_Objects|")
    ("|Free Variables in Top-Level Input|"
     . "|Free_Variables_in_Top-Level_Input|")
    ("|Flawed Induction Candidates in App Example|"
     .
     "|Flawed_Induction_Candidates_in_App_Example|")
    ("|Evaluating App on Sample Input|" . "|Evaluating_App_on_Sample_Input|")
    ("|Corroborating Models|" . "|Corroborating_Models|")
    ("|Common Lisp as a Modeling Language|"
     .
     "|Common_Lisp_as_a_Modeling_Language|")
    ("|Common Lisp|" . "|Common_Lisp|")
    ("|Analyzing Common Lisp Models|" . "|Analyzing_Common_Lisp_Models|")
    ("|An Example of ACL2 in Use|" . "|An_Example_of_ACL2_in_Use|")
    ("|An Example Common Lisp Function Definition|"
     .
     "|An_Example_Common_Lisp_Function_Definition|")
    ("|About the Prompt|" . "|About_the_Prompt|")
    ("|About the Admission of Recursive Definitions|"
     .
     "|About_the_Admission_of_Recursive_Definitions|")
    ("|About the ACL2 Home Page|" . "|About_the_ACL2_Home_Page|")
    ("|About Types|" . "|About_Types|")
    ("|About Models|" . "|About_Models|")
    ("|ACL2 is an Untyped Language|" . "|ACL2_is_an_Untyped_Language|")
    ("|ACL2 as an Interactive Theorem Prover (cont)|"
     .
     "|ACL2_as_an_Interactive_Theorem_Prover_(cont)|")
    ("|ACL2 as an Interactive Theorem Prover|"
     .
     "|ACL2_as_an_Interactive_Theorem_Prover|")
    ("|ACL2 System Architecture|" . "|ACL2_System_Architecture|")
    ("|ACL2 Symbols|" . "|ACL2_Symbols|")
    ("|ACL2 Strings|" . "|ACL2_Strings|")
    ("|ACL2 Conses or Ordered Pairs|" . "|ACL2_Conses_or_Ordered_Pairs|")
    ("|ACL2 Characters|" . "|ACL2_Characters|")
    ("|A Walking Tour of ACL2|" . "|A_Walking_Tour_of_ACL2|")
    ("|A Typical State|" . "|A_Typical_State|")
    ("|A Trivial Proof|" . "|A_Trivial_Proof|")
    ("|A Tiny Warning Sign|" . "|A_Tiny_Warning_Sign|")
    ("|A Sketch of How the Rewriter Works|"
     .
     "|A_Sketch_of_How_the_Rewriter_Works|")
    ("|A Flying Tour of ACL2|" . "|A_Flying_Tour_of_ACL2|")))

(defun just-one-space-across-newlines ()
  "Delete all spaces, tabs and newlines around point, leaving one space."
  (interactive)
  (let ((point (point)))

    ;; Replace a white character at point and any trailing whitespace
    ;; by a single space.

    (if (and (re-search-forward "[ \t\n]+" nil t)
             (equal point (match-beginning 0)))
        (replace-match " "))

    ;; Replace leading whitespace (if any) and a black character at
    ;; point by a single space followed by the black character.

    (goto-char point)

    (cond
     ;; First look for <black white*> just before, or including point;
     ;; if found, replace it by <black blank>.

     ((and (re-search-backward "\\([^ \t\n]\\)[ \t\n]*" nil t))
      (if (equal (match-end 0) point)
          (if (equal (buffer-substring point (1+ point)) " ")
              (replace-match "\\1")
            (replace-match "\\1 "))))

     ;; Failing that, look for <start-of-buffer white*> just before,
     ;; or including point; if found, replace it by <start-of-buffer
     ;; blank>.

     (t
      (goto-char (point-min))
      (if (and (re-search-forward "[ \t\n]*" nil t)
               (or (equal (match-end 0) point)
                   (equal (match-end 0) (1+ point))))
          (replace-match "\\1 "))))))

(defun fix ()
  (interactive)

  ;; set fill column (buffer-local)
  (setq fill-column 79)

  (lisp-mode)

  ;; not sure this is needed, but just to be safe:
  (auto-fill-mode -1)

  ;; fix up extra whitespace in <code> blocks, etc.
  (delete-trailing-whitespace)

  ;; replace spaces with underscores in topic names that have a space
  (message "(0) replace spaces ...")
  (let ((alist *doc-fix-alist*))
    (while alist
      (goto-char (point-min))
      (while (search-forward (car (car alist)) nil t)
	(replace-match (cdr (car alist)) nil t)
	(message "[%s] replaced spaces ..."
		 (- (length *doc-fix-alist*)
		    (length alist))))
      (setq alist (cdr alist))))

  ;; make sure P tags and CODE tags are separated by at least a newline,
  ;; to avoid fill-paragraph ruining code blocks

  (goto-char (point-min))
  (message "(1) replace-string ...")
  (replace-string "<p>
<code>" "<p>

<code>")

  (goto-char (point-min))
  (message "(2) replace-string ...")
  (replace-string "</code>
</p>" "</code>

</p>")

  (goto-char (point-min))
  (message "(3) replace-string ...")
  (replace-string "<p>
@({"
		  "<p>

@({")

  (goto-char (point-min))
  (message "(4) replace-string ...")
  (replace-string "})
</p>"
		  "})

</p>")

  ;; run fill-paragraph after every <p> tag to try to fix most
  ;; word-wrapping, using ordinary fill-paragraph so as to avoid
  ;; problems with left parentheses, for example this problem with
  ;; (defxdoc |ACL2 Symbols| ...):

; <p>Technically, a symbol is a special kind of pair consisting of a package
; name
; (which is a string) and a symbol name (which is also a string).

  ;; But we use the fill-paragraph for lisp-mode when at the start, so
  ;; that we don't fill back to "(defxdoc".

  (goto-char (point-min))
  (message "(5) fill-paragraph after every <p>")
  (while (search-forward "<p>" (point-max) t)
    (if (equal (char-before (match-beginning 0))
	       ?\")
	(fill-paragraph)
      (let ((fill-paragraph-function t))
	(fill-paragraph))))

  ;; run fill-paragraph near every </p> tag to get some additional paragraphs
  (goto-char (point-min))
  (message "(6) fill-paragraph after every </p>")
  (while (search-forward "</p>" (point-max) t)
    (search-backward "<")
    (fill-paragraph)
    (search-forward ">"))

  ;; run fill-paragraph some more, in places that seem like they are safely not
  ;; within <code> or @({...}) areas
  (goto-char (point-min))
  (message "(7) fill-paragraph some more")
  (while (search-forward "@('" (point-max) t)
    (fill-paragraph))

  ;; fix up extra space at many paragraph starts
  (goto-char (point-min))
  (message "(8) fix up extra space at many paragraph starts")
  (replace-string "<p> " "<p>")

  ;; fix up empty paragraphs that frequently occur
  (goto-char (point-min))
  (message "(9) fix up empty paragraphs that frequently occur")
  (replace-string "<p></p>" "")

  ;; eat extra space at the start of :long topics
  (goto-char (point-min))
  (message "(10) eat extra space at the start of :long topics")
  (while (search-forward ":long \"" (point-max) t)
    (just-one-space-across-newlines))

  ;; normalize short strings
  (message "(11) normalize short strings")
  (while (search-forward ":short \"" (point-max) t)
    (fill-paragraph))

  ;; the above change every :long to have one space in front of it, so eat
  ;; that unnecessary space, now.
  (goto-char (point-min))
  (message "(12) replace-string")
  (replace-string ":long \" " ":long \"")

; The remaining steps are a final bit of clean up added by Matt.
; There is likely a more elegant way to accomplish this, by doing
; things earlier that prevent making this mess.  But for this one-off
; tool I think this is good enough.

  ;; eliminate lines with a single space
  (goto-char (point-min))
  (message "(13) eliminate excess blank lines between paragraphs")
  (while (search-forward "
 
" nil t)
    (setq found t)
    (replace-match "

" nil t))

  ;; eliminate excess blank lines after paragraphs
  (message "(14) eliminate excess blank lines between paragraphs")
  (let ((found t))
    (while found
      (setq found nil)
      (goto-char (point-min))
      (while (search-forward "</p>


" nil t)
	(setq found t)
	(replace-match "</p>

" nil t))))

  ;; eliminate excess blank lines before paragraphs
  (message "(15) eliminate excess blank lines before paragraphs")
  (let ((found t))
    (while found
      (setq found nil)
      (goto-char (point-min))
      (while (search-forward "


 <p>" nil t)
	(setq found t)
	(replace-match "

 <p>" nil t))))

  ;; eliminate excess spaces before end of paragraph
  (message "(16) eliminate excess spaces before end of paragraph")
  (let ((found t))
    (while found
      (setq found nil)
      (goto-char (point-min))
      (while (re-search-forward "[ \n]</p>" nil t)
	(setq found t)
	(replace-match "</p>" nil t))))

  ;; fix up empty paragraphs that frequently occur (again)
  (goto-char (point-min))
  (message "(17) fix up empty paragraphs that frequently occur (again)")
  (replace-string "<p></p>" "")

  (goto-char (point-min))
  (message "(18) fill-paragraph again after every initial <p>")
  (while (search-forward "<p>" (point-max) t)
    (if (equal (char-before (match-beginning 0))
	       ?\")
	(fill-paragraph)
      (let ((fill-paragraph-function t))
	(fill-paragraph))))

; Do this last:
  (message "(19) restore spaces ...")
  (let ((alist *doc-fix-alist*))
    (while alist
      (goto-char (point-min))
      (while (search-forward (cdr (car alist)) nil t)
	(replace-match (car (car alist)) nil t))
      (setq alist (cdr alist))))

  (message "DONE!")
  )
