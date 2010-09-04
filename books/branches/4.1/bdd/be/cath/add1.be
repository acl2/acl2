@BE1
@invar
(CARRYIN A[1] A[2] A[3] A[4] B[1] B[2] B[3] B[4])
@sub
 N3 = (A[1])
 N4 = (A[3])
 N5 = (A[2])
 N6 = (A[4])
 N7 = (not CARRYIN)
 N8 = (B[3])
 N9 = (B[1])
 N10 = (B[2])
 N11 = (B[4])
 N17 = (OR (AND (NOT N3))) 
 N31 = (OR (AND (NOT N4))) 
 N29 = (OR (AND (NOT N5))) 
 N19 = (OR (AND (NOT N7)) (AND (NOT N7))) 
 N43 = (OR (AND (NOT N6))) 
 N20 = (OR (AND (NOT N19))) 
 N18 = (NOT (OR (AND N9 (NOT N3)) (AND (NOT N9) N3))) 
 N28 = (NOT (OR (AND N10 (NOT N5)) (AND (NOT N10) N5))) 
 N32 = (NOT (OR (AND N8 (NOT N4)) (AND (NOT N8) N4))) 
 N16 = (OR (AND (NOT N18))) 
 N24 = (OR (AND (NOT N28))) 
 N22 = (OR (AND (NOT N16))) 
 N42 = (NOT (OR (AND N11 (NOT N6)) (AND (NOT N11) N6))) 
 N38 = (OR (AND (NOT N42)))
 N27 = (OR (AND (NOT N24))) 
 N21 = (NOT (OR (AND N20 N16) (AND (NOT N20)  (NOT N16)))) 
 N23 = (OR (AND (NOT N16) (NOT N3)) (AND (NOT N22) (NOT N19))) 
 N25 = (OR (AND (NOT N23))) 
 N26 = (NOT (OR (AND N25 (NOT  N24)) (AND (NOT N25) N24))) 
 N13 = (OR (AND (NOT N26))) 
 N30 = (OR (AND (NOT N32))) 
 N33 = (OR (AND (NOT N27) (NOT N23)) (AND (NOT N29) (NOT N24))) 
 N36 = (OR (AND (NOT N30))) 
 N15 = (OR (AND (NOT N21))) 
 N34 = (OR (AND (NOT N33))) 
 N41 = (OR (AND (NOT N38))) 
 N37 = (OR (AND (NOT N30) (NOT N4)) (AND (NOT N36) (NOT N33))) 
 N39 = (OR (AND (NOT N37))) 
 N40 = (NOT (OR (AND N39 (NOT N38)) (AND (NOT N39) N38))) 
 N12 = (OR (AND (NOT N40))) 
 N35 = (NOT (OR (AND N34 N30) (AND (NOT N34) (NOT N30)))) 
 N14 = (OR (AND (NOT N35)))
 N44 = (OR (AND (NOT N41) (NOT N37)) (AND (NOT N43) (NOT N38))) 
@out
O[1] = (N15)                                                          
O[2] = (N13)
O[3] = (N14)
O[4] = (N12)
COUT = (N44)
@end



@BE2
@invar
(CARRYIN A[1] B[1] A[2] B[2] A[3] B[3] A[4] B[4])

@sub
COUT1 = 
(OR (AND CARRYIN B[1]) (AND  CARRYIN A[1]) (AND B[1] A[1]))
COUT2 =
(OR (AND COUT1 B[2]) (AND  COUT1 A[2]) (AND B[2] A[2]))
COUT3 = 
(OR (AND COUT2 B[3]) (AND COUT2 A[3]) (AND B[3] A[3]))

@out
O[1] = (EXOR A[1] B[1]  CARRYIN)
O[2] = (EXOR A[2] B[2]  COUT1)
O[3] = (EXOR A[3] B[3]  COUT2)
O[4] = (EXOR A[4] B[4]  COUT3)
COUT = 
 (OR (AND  COUT3 B[4]) (AND  COUT3 A[4]) (AND B[4] A[4]))

@end
