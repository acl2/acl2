Const
  n: 30;

Type
  Msg:   enum { null, req_sh, req_ex, inv, inv_ack, gr_sh, gr_ex };
  State: enum { I, S, E };
  ID:    Scalarset(n);

Var
  ch1: array[ID] of Msg;                  /* channel 1 */
  ch2: array[ID] of Msg;                  /* channel 2 */
  ch3: array[ID] of Msg;                  /* channel 3 */
  hsl: array[ID] of boolean;              /* home_shared_list */
  hil: array[ID] of boolean;              /* home_invalidate_list */
  heg: boolean;                           /* home_exclusive_granted */
  hcm: Msg;                               /* home_current_command */
  hcc: ID;                                /* home_current_client */
  c:   array[ID] of State;                /* distributed cache state */


Ruleset i: ID do

  rule "1" /* client requests shared access */
  c[i] = I & ch1[i] = null ==>
  begin
    ch1[i] := req_sh;
  end;

  rule "2" /* client requests exclusive access */
  c[i] = I & ch1[i] = null ==>
  begin
    ch1[i] := req_ex;
  end;

  rule "3" /* home picks new request */
  hcm = null & ch1[i] != null ==>
  begin
    hcm := ch1[i];
    ch1[i] := null;
    hcc := i;
    for j: ID do
      hil[j] := hsl[j];
    end;
  end;

  rule "4" /* home sends invalidate message */
  hil[i] & ch2[i] = null & ((hcm = req_sh & heg) | hcm = req_ex) ==>
  begin
    ch2[i] := inv;
    hil[i] := false;
  end;

  rule "5" /* home receives invalidate acknowledgement */
  hcm != null & ch3[i] = inv_ack ==>
  begin
    hsl[i] := false;
    heg := false;
    ch3[i] := null;
  end;

  rule "6" /* sharer invalidates cache */
  ch2[i] = inv & ch3[i] = null ==>
  begin
    ch2[i] := null;
    ch3[i] := inv_ack;
    c[i] := I;
  end;

  rule "7" /* client receives shared grant */
  ch2[i] = gr_sh ==>
  begin
    c[i] := S;
    ch2[i] := null;
  end;

  rule "8" /* client receives exclusive grant */
  ch2[i] = gr_ex ==>
  begin
    c[i] := E;
    ch2[i] := null;
  end;

end; /* ruleset */

rule "9" /* home grants share */
  hcm = req_sh & !heg & ch2[hcc] = null ==>
  begin
    hsl[hcc] := true;
    hcm := null;
    ch2[hcc] := gr_sh;
  end;

rule "10" /* home grants exclusive */
  hcm = req_ex & (forall i: ID do hsl[i] = false end) & ch2[hcc] = null ==>
  begin
    hsl[hcc] := true;
    hcm := null;
    heg := true;
    ch2[hcc] := gr_ex;
  end;


startstate
  begin
    for i: ID do
      ch1[i] := null;
      ch2[i] := null;
      ch3[i] := null;
      c[i] := I;
      hsl[i] := false;
      hil[i] := false;
    end;
    hcm := null;
    hcc := undefined;
    heg := false;
  end;

Invariant
  forall i: ID do
    c[i] = E ->
      forall j: ID do
        j != i -> c[j] = I
      end
  end
