@BE1

@invar
 (A1 B1 A2 B2)

@sub
CAR1 = 
(AND A1 B1)

@out
SOM1 = 
(EXOR A1 B1)
SOM2 = 
(EXOR A2 B2 CAR1)
COUT = 
(OR (AND (OR A2 B2) CAR1) (AND A2 B2))
@end


@BE2

@invar
 (A1 B1 A2 B2)

@sub
COUT1 = 
(AND B1 A1)

@out
SOM1 = 
(NOT (OR (AND (NOT A1) (NOT B1)) (AND A1 B1))) 
SOM2 = 
(NOT (OR (AND (OR (AND (NOT A2) (NOT B2)) (AND A2 B2)) (NOT COUT1)) (AND COUT1 (NOT (OR (AND (NOT A2) (NOT B2)) (AND A2 B2)))))) 
COUT = 
(OR (AND A2 COUT1) (AND B2 COUT1) (AND A2 B2)) 
@end
