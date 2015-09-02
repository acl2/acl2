;;; This is a supporting file for Chapter 11, "Using Macros to Mimic
;;; VHDL", by Dominique Borrione, Philippe Georgelin, and Vanderlei
;;; Rodrigues, in "Computer-Aided Reasoning: ACL2 Case Studies",
;;; edited by M. Kaufmann, P. Manolios, J Moore (Kluwer, 2000,
;;; p.167-182).

(in-package "ACL2")

(include-book "vhdl")

(vhdl

 (_entity mycomp :port
     (arg :in natural
      start :in bit
      clk :in bit
      result :out natural
      done :out bit))

 (_architecture fact :of mycomp :is
     ((_signal op1 :type natural)
      (_signal op2 :type natural)
      (_signal resmult :type natural)
      (_signal startmult :type bit)
      (_signal endmult :type bit))
  :begin

     ((_process multiplier :is ()
       :begin
	  ((_wait :until (equal clk 1))
           (_if (equal startmult 1)
	    :then
	       ((_<= resmult (* op1 op2))))
	   (_<= endmult startmult)))

      (_process doit :is
	  ((_variable mystate :type natural := 0)
 	   (_variable r :type natural := 0)
	   (_variable f :type natural := 0))
       :begin
          ((_wait :until (equal clk 1))
	   (_if (equal mystate 0)
	    :then
               ((_<- r arg)
		(_<- f 1)
		(_if (equal start 1)
		 :then
		    ((_<- mystate 1))))
	    :else
	       ((_if (equal mystate 1)
		 :then
		    ((_if (equal r 1)
		      :then
		         ((_<= result f)
			  (_<= done 1)
			  (_<- mystate 0))
		      :else
		         ((_<= startmult 1)
			  (_<= op1 r)
			  (_<= op2 f)
			  (_<- mystate 2))))
		 :else
		    ((_if (equal mystate 2)
		      :then
                         ((_if (equal endmult 1)
		           :then
		              ((_<- f resmult)
			       (_<- r (- r 1))
			       (_<= startmult 0)
			       (_<- mystate 1))))))))))))))


