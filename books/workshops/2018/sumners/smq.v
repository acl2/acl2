// smq.v
//
// This is a simple-memory queue which processes reads and writes with
// certain ordering and blocking requirements. We attempt to catch
// deadlock failures with our check in this case.

`define TAG_SIZE 4
`define ADDR_SIZE 16
`define DATA_SIZE 16
`define TAG_RNG 3:0
`define TAG_VEC 15:0
`define NUM_TAGS 16
`define ADDR_RNG 15:0
`define DATA_RNG 15:0

`define RWQ_SIZE 16
`define RWQ_RNG 15:0

`define STATE_RNG 1:0
`define CNTR_RNG 3:0
`define CNTR_SIZE 4
`define STATE_REQ 0
`define STATE_WAIT 1
`define STATE_RESP 2
`define STATE_DONE 3

`define BYPASS_THRESHOLD 2
`define WR_BURST_THRESHOLD 2

module smq
  (input clk,
   input reset,
   ///////// ***** PORTS for SRQ RTL ******  /////////
   // source incoming command
   input                  src_cmd_val,
   input                  src_is_read,
   input [`TAG_RNG]       src_tag,
   input [`ADDR_RNG]      src_addr,
   input [`DATA_RNG]      src_data,
   // source outgoing response
   output reg             src_resp_val,
   output reg [`TAG_RNG]  src_resp_tag,
   output reg [`DATA_RNG] src_resp_data,
   // dest outgoing command
   output reg             dest_cmd_val,
   output reg             dest_is_read,
   output reg [`ADDR_RNG] dest_addr,
   output reg [`DATA_RNG] dest_data,
   output reg [`TAG_RNG]  dest_tag,
   // dest incoming response
   input                  dest_resp_val,
   input [`TAG_RNG]       dest_resp_tag,
   input [`DATA_RNG]      dest_resp_data
   );
   
   ///////// ***** ORIGINAL RTL definition for SMQ (updated with some fixes) ******  /////////
         
   // a queue of reads and writes coming from a "source" (think CPU) to 
   //                                         a "destination" (think MEM).
   //
   // 1. reads can pass writes except:
   //    a. when in burst mode where writes get strict priority
   //    b. when another oldest read or write are in forced mode
   // 2. reads/writes cannot pass other writes to the same address
   //
   // the entries in the queue are created from new commands received from the source..
   // are then sent to the destination.. wait for response from destination.. and then
   // send response to the source.
   
   reg [`RWQ_RNG]         rwq_val;
   reg [`RWQ_RNG]         rwq_is_read;
   reg [`ADDR_RNG]        rwq_addr[`RWQ_RNG];
   reg [`TAG_RNG]         rwq_srctag[`RWQ_RNG];
   reg [`DATA_RNG]        rwq_data[`RWQ_RNG];
   reg [`STATE_RNG]       rwq_state[`RWQ_RNG];
   reg [`RWQ_RNG]         rwq_in_burst;
   reg [`RWQ_RNG]         rwq_older[`RWQ_RNG];
   reg [`RWQ_RNG]         rwq_match_older[`RWQ_RNG];
   reg [`RWQ_RNG]         rwq_older_rdx;
   reg [`RWQ_RNG]         rwq_match_older_rdx;
   reg [`CNTR_RNG]        rwq_bypass_cntr;
   reg                    rwq_forced;

   reg                    in_burst_mode;
   reg [`RWQ_RNG]         read_can_go;
   reg [`RWQ_RNG]         entry_blk;
   reg [`RWQ_RNG]         entry_rdy;
   reg [`RWQ_RNG]         rwq_write_blk;
   reg [`RWQ_RNG]         rwq_force_blk;
   reg [`RWQ_RNG]         rwq_read_blk;
   reg [`CNTR_RNG]        num_writes_rwq;
   reg [`RWQ_RNG]         oldest_entry;
   reg [`RWQ_RNG]         rwq_state_req;
   reg [`RWQ_RNG]         rwq_state_resp;
   reg [`RWQ_RNG]         rwq_state_done;
   reg [`RWQ_RNG]         rwq_state_done_d1;
   reg [`RWQ_RNG]         src_addr_match;   

   reg [`RWQ_RNG]         lower_slots[`RWQ_RNG];
   reg [`RWQ_RNG]         slot_avail;
   reg [`RWQ_RNG]         req_ready;
   reg [`RWQ_RNG]         resp_ready;
   reg [`RWQ_RNG]         new_slot;
   reg [`RWQ_RNG]         grant_req;
   reg [`RWQ_RNG]         grant_resp;

   // We now define the update logic for the flops of the scheduling queue.. The main logic of the simple scheduler..
   // The next state for the schedulinq queue is computed as the result of the following sequence of steps:
   //
   // 1. set upd value to current queue state
   // 2. mark done entries invalid
   // 3. update in_burst setting which commands are in burst mode
   // 4. handle incoming responses from dest
   // 5. send source outgoing for read results
   // 6. send dest outgoing for ready reads/writes
   // 7. load any new commands
   
   always@(posedge clk)
     if (reset | ~|grant_resp) begin
        src_resp_val <= 1'b0;
     end
     else begin
        for (int i=0; i<`RWQ_SIZE; i=i+1) begin
           if (grant_resp[i]) begin
              src_resp_val  <= 1'b1;
              src_resp_tag  <= rwq_srctag[i];
              src_resp_data <= rwq_data[i];
           end
        end
     end // else: !if(reset | ~|grant_resp)
   
   always@(posedge clk)
     if (reset | ~|grant_req) begin
        dest_cmd_val <= 1'b0;
     end
     else begin
        for (int i=0; i<`RWQ_SIZE; i=i+1) begin
           if (grant_req[i]) begin
              dest_cmd_val <= 1'b1;
              dest_is_read <= rwq_is_read[i];
              dest_addr    <= rwq_addr[i];
              dest_tag     <= rwq_srctag[i];
              dest_data    <= rwq_data[i];
           end
        end
     end // else: !if(reset | ~|grant_req)

   always@(posedge clk)
     rwq_val <= {`RWQ_SIZE{~reset}} &
                ((~rwq_val & {`RWQ_SIZE{src_cmd_val}} & new_slot) |
                 (rwq_val & ~rwq_state_done));

   // is_read, addr, srctag, data, state
   always@(posedge clk)
     for (int i=0; i<`RWQ_SIZE; i=i+1) begin
        if (reset) begin
           rwq_is_read[i] <= 1'b0;
           rwq_addr[i]    <= 0;
           rwq_srctag[i]  <= 0;
           rwq_data[i]    <= 0;
           rwq_state[i]   <= 0;
        end
        else if (~rwq_val[i]) begin
           if (src_cmd_val & new_slot[i]) begin
              rwq_is_read[i] <= src_is_read;
              rwq_addr[i]    <= src_addr;
              rwq_srctag[i]  <= src_tag;
              rwq_data[i]    <= src_data;
              rwq_state[i]   <= `STATE_REQ;
           end
        end
        else if (rwq_val[i]) begin
           if (rwq_state[i] == `STATE_REQ) begin
              if (grant_req[i]) rwq_state[i] <= `STATE_WAIT;
           end
           else if (rwq_state[i] == `STATE_WAIT) begin
              if (dest_resp_val & (rwq_srctag[i] == dest_resp_tag)) begin
                 rwq_state[i] <= `STATE_RESP;
                 rwq_data[i] <= dest_resp_data;
              end
           end
           else if (rwq_state[i] == `STATE_RESP) begin
              if (grant_resp[i]) rwq_state[i] <= `STATE_DONE;
           end
        end // if (rwq_val[i])
     end // for (int i=0; i<`RWQ_SIZE; i=i+1)

   always@*
     for (int i=0; i<`RWQ_SIZE; i=i+1)
       src_addr_match[i] = (rwq_addr[i] == src_addr);
     
   // rwq_older, rwq_match_older
   always@(posedge clk)
     for (int i=0; i<`RWQ_SIZE; i=i+1) begin
       if (reset) begin
          rwq_older[i] <= {`RWQ_SIZE{1'b0}};
          rwq_match_older[i] <= {`RWQ_SIZE{1'b0}};
       end
       else if (~rwq_val[i]) begin
          if (src_cmd_val & new_slot[i]) begin
             rwq_older[i] <= rwq_val;
             rwq_match_older[i] <= rwq_val & src_addr_match;
          end
       end
       else if (rwq_val[i]) begin
          rwq_older[i] <= rwq_older[i] & rwq_val;
          rwq_match_older[i] <= rwq_match_older[i] & rwq_val;
       end
     end // for (int i=0; i<`RWQ_SIZE; i=i+1)

   always@(posedge clk)
     for (int i=0; i<`RWQ_SIZE; i=i+1)
       lower_slots[i] <= (16'b1 << i) - 16'b1;

   always@* slot_avail  = ~rwq_val;
   always@* req_ready   = rwq_val & entry_rdy;
   always@* resp_ready  = rwq_val & rwq_state_resp & ~rwq_older_rdx;
   
   always@*
     for (int i=0; i<`RWQ_SIZE; i=i+1)
       new_slot[i] = slot_avail[i] & ~|(lower_slots[i] & slot_avail);

   always@*
     for (int i=0; i<`RWQ_SIZE; i=i+1)
       grant_req[i] = req_ready[i] & ~|(lower_slots[i] & req_ready);

   always@*
     for (int i=0; i<`RWQ_SIZE; i=i+1)
       grant_resp[i] = resp_ready[i] & ~|(lower_slots[i] & resp_ready);

   // always@* read_can_go = rwq_val & rwq_is_read;
   // BUG, the line above should be the one below, or otherwise,
   // we can get a deadlock cycle:
   always@* read_can_go = rwq_val & rwq_is_read & ~rwq_match_older_rdx;
   
   // Simple vector defining whether an entry is blocked during force mode:
   // Logic for defining when a write is "blocked" in order to process a read in the queue:
   // and for when a read is blocked (only in write burst mode):

   always@* rwq_force_blk = rwq_older_rdx & {`RWQ_SIZE{rwq_forced}};
   always@* rwq_write_blk = ~rwq_is_read  & (in_burst_mode ? ~rwq_in_burst : {`RWQ_SIZE{|read_can_go}});
   always@* rwq_read_blk  =  rwq_is_read  & {`RWQ_SIZE{in_burst_mode}};
   
   // Main queue entry "ready" logic which defines when an entry is ready to be picked to be sent to the
   // destination.. There is no pipeline and so an entry which is ready will be sent immediately..
   always@*
     for (int i=0; i<`RWQ_SIZE; i=i+1) begin
        rwq_state_req[i]  = (rwq_state[i] == `STATE_REQ);
        rwq_state_resp[i] = (rwq_state[i] == `STATE_RESP);
        rwq_state_done[i] = (rwq_state[i] == `STATE_DONE);
     end

   always@(posedge clk) rwq_state_done_d1 <= rwq_state_done;

   always@*
     for (int i=0; i<`RWQ_SIZE; i=i+1) begin
        rwq_match_older_rdx[i] = |rwq_match_older[i];
        rwq_older_rdx[i]       = |rwq_older[i];
     end

   always@* entry_blk = rwq_match_older_rdx | rwq_force_blk | rwq_read_blk | rwq_write_blk;
   always@* entry_rdy = rwq_val & rwq_state_req & ~entry_blk;

   always@*
     for (int i=0; i<`RWQ_SIZE; i=i+1)
       oldest_entry[i] = ~(|(rwq_older[i]));
   
   // A simple counter of the number of times that the oldest entry is bypassed:
   always@(posedge clk)
     if (reset | |(entry_rdy & oldest_entry))
       rwq_bypass_cntr <= 4'd0;
     else if (|entry_rdy & (rwq_bypass_cntr <= `BYPASS_THRESHOLD))
       rwq_bypass_cntr <= rwq_bypass_cntr + 4'd1;
   
   // We go into "forced" mode when the oldest entry in the queue has been bypassed enough times:
   always@*
     if (reset | |(entry_rdy & oldest_entry))
       rwq_forced <= 1'b0;
     else if ((rwq_bypass_cntr >= `BYPASS_THRESHOLD) & ~in_burst_mode)
       rwq_forced <= 1'b1;
   
   // A counter for the number of writes currently in the queue:
   always@* begin
      num_writes_rwq = 4'd0;
      for (int i=0; i<`RWQ_SIZE; i=i+1)
        if (rwq_val[i] & rwq_is_read[i] & (rwq_state[i] != `STATE_DONE))
          num_writes_rwq = num_writes_rwq + 4'd1;
   end
   
   // Logic defining "burst" mode where we force writes out of the queue if enough of them have stacked up:
   always@* in_burst_mode = |rwq_in_burst;
   
   always@(posedge clk)
     for (int i=0; i<`RWQ_SIZE; i=i+1)
       if (reset | (rwq_in_burst[i] & (~rwq_val[i] | (rwq_state[i] == `STATE_DONE))))
         rwq_in_burst[i] <= 1'b0;
       else if (rwq_val[i] & ~rwq_is_read[i] & ~rwq_in_burst[i] & ~rwq_match_older_rdx[i]
                & ~in_burst_mode & (num_writes_rwq >= `WR_BURST_THRESHOLD) & ~rwq_forced)
         rwq_in_burst[i] <= 1'b1;

endmodule // smq

module top
  (input clk,
   input reset,
   ///////// ***** PORTS for SRQ RTL ******  /////////
   // source incoming command
   input [1:0]            rand_src_cmd_val,
   input                  rand_src_is_read,
   input [`TAG_RNG]       rand_src_tag,
   input [`ADDR_RNG]      rand_src_addr,
   input [`DATA_RNG]      rand_src_data,
   // dest incoming response
   input                  rand_dest_resp_val,
   input [`TAG_RNG]       rand_dest_resp_tag,
   input [`DATA_RNG]      rand_dest_resp_data,
   // free inputs for the transforms
   input                  free_addr_select,
   input                  free_burst_select,
   input                  free_src_delay,
   input                  free_dest_delay
);

   // input connections to the SMQ des instance:
   reg                    src_cmd_val;
   reg                    src_is_read;
   reg [`TAG_RNG]         src_tag;
   reg [`ADDR_RNG]        src_addr;
   reg [`DATA_RNG]        src_data;
   reg                    dest_resp_val;
   reg [`TAG_RNG]         dest_resp_tag;
   reg [`DATA_RNG]        dest_resp_data;

   // output connections to the SMQ des instance:
   wire                   src_resp_val;
   wire [`TAG_RNG]        src_resp_tag;
   wire [`DATA_RNG]       src_resp_data;
   wire                   dest_cmd_val;
   wire                   dest_is_read;
   wire [`ADDR_RNG]       dest_addr;
   wire [`DATA_RNG]       dest_data;
   wire [`TAG_RNG]        dest_tag;

   // the failure signal we are trying to check:
   reg                    fail_out;
   wire                   reqs_stalled;

   // variables needed to define the tag-selection
   // environment modeling:
   reg [`TAG_VEC]         src_tags;
   reg [`TAG_VEC]         dest_tags;
   reg [`TAG_RNG]         next_src_tag;
   reg [`TAG_RNG]         next_dest_tag;
   reg                    found_src_tag;
   reg                    found_dest_tag;
   
   // the outputs from the environment modeling and
   // random inputs.. these represent what would
   // normally come from waves but are random in this
   // case:
   reg                    src_cmd_val0;
   reg                    src_is_read0;
   reg [`TAG_RNG]         src_tag0;
   reg [`ADDR_RNG]        src_addr0;
   reg [`DATA_RNG]        src_data0;
   reg                    dest_resp_val0;
   reg [`TAG_RNG]         dest_resp_tag0;
   reg [`DATA_RNG]        dest_resp_data0;

   // variables for the first input transform:
   reg                    focal_addr_picked;
   reg [`ADDR_RNG]        focal_addr;
   reg [`ADDR_RNG]        pick_src_addr;
   reg                    src_cmd_val1;
   reg                    src_is_read1;
   reg [`TAG_RNG]         src_tag1;
   reg [`ADDR_RNG]        src_addr1;
   reg [`DATA_RNG]        src_data1;
   reg                    dest_resp_val1;
   reg [`TAG_RNG]         dest_resp_tag1;
   reg [`DATA_RNG]        dest_resp_data1;

   // variables for the second input transform:
   reg                    last_valid_is_read;
   reg                    pick_src_cmd;
   reg                    src_cmd_val2;
   reg                    src_is_read2;
   reg [`TAG_RNG]         src_tag2;
   reg [`ADDR_RNG]        src_addr2;
   reg [`DATA_RNG]        src_data2;
   reg                    dest_resp_val2;
   reg [`TAG_RNG]         dest_resp_tag2;
   reg [`DATA_RNG]        dest_resp_data2;

   // variables for the third input transform:
   reg                    src_cmd_val_h;
   reg                    src_is_read_h;
   reg [`TAG_RNG]         src_tag_h;
   reg [`ADDR_RNG]        src_addr_h;
   reg [`DATA_RNG]        src_data_h;
   reg                    src_cmd_val_d;
   reg                    src_is_read_d;
   reg [`TAG_RNG]         src_tag_d;
   reg [`ADDR_RNG]        src_addr_d;
   reg [`DATA_RNG]        src_data_d;
   reg                    release_src;
   reg                    hold_new_src;
   reg                    pick_src_hold;
   reg                    src_hold;
   reg                    dest_resp_val_h;
   reg [`TAG_RNG]         dest_resp_tag_h;
   reg [`DATA_RNG]        dest_resp_data_h;
   reg                    dest_resp_val_d;
   reg [`TAG_RNG]         dest_resp_tag_d;
   reg [`DATA_RNG]        dest_resp_data_d;
   reg                    release_dest;
   reg                    hold_new_dest;
   reg                    pick_dest_hold;
   reg                    dest_hold;
   reg                    src_cmd_val3;
   reg                    src_is_read3;
   reg [`TAG_RNG]         src_tag3;
   reg [`ADDR_RNG]        src_addr3;
   reg [`DATA_RNG]        src_data3;
   reg                    dest_resp_val3;
   reg [`TAG_RNG]         dest_resp_tag3;
   reg [`DATA_RNG]        dest_resp_data3;

   //
   // Our goal is to fail if we ever reach a state where we have rwq entries
   // that are valid but nothing is marked as rdy so nothing makes progress..
   //
   // Instead of taking an incoming wave input for this example, we will use
   // random inputs for most of the inputs, and then do transformations on those
   // using random/constrained inputs with a few free variable inputs that drive
   // the decisions of the input transformations.
   //
   // The input transformation consists of the following primary effects:
   //
   // 1. Value mapping to select previously chosen selected special values.
   //    We will do this for the address input.
   // 2. Bursting created by changing the input command (in this case, just
   //    reads and writes) to match the immediately previous command.
   // 3. Delay injection which decides whether to delay an incoming req/resp
   //    assuming there is a slot where it can delay it
   //
   // In addition, we just add simple modeling for tags coming from each interface.
   //

   //////////////////////////////////////////////
   // ENVIRONMENT for tag modeling:
   //////////////////////////////////////////////
   //
   //
   // We add some modeling logic to keep track of tags that we have sent in
   // from the src interface (to avoid repeats) and we have seen at the
   // dest interface (so responses use matching tags):
   
   always@(posedge clk)
     src_tags <= (((src_tags 
                    | ({`NUM_TAGS{src_cmd_val}}  & (16'b1 << src_tag)))
                   & ~({`NUM_TAGS{src_resp_val}} & (16'b1 << src_resp_tag)))
                  & {`NUM_TAGS{~reset}});

   always@(posedge clk)
     dest_tags <= (((dest_tags 
                     | ({`NUM_TAGS{dest_cmd_val}}  & (16'b1 << dest_tag)))
                    & ~({`NUM_TAGS{dest_resp_val}} & (16'b1 << dest_resp_tag)))
                   & {`NUM_TAGS{~reset}});
   
   always@* begin
      found_src_tag = 1'b0;
      next_src_tag = 0;
      for (int i=0; i<`NUM_TAGS; i++) begin
        if (~found_src_tag & ~src_tags[i]) begin
           found_src_tag = 1'b1;
           next_src_tag = i;
        end
      end
   end
   
   always@* begin
      found_dest_tag = 1'b0;
      next_dest_tag = 0;
      for (int i=0; i<`NUM_TAGS; i++) begin
        if (~found_dest_tag & dest_tags[i]) begin
           found_dest_tag = 1'b1;
           next_dest_tag = i;
        end
      end
   end

   //////////////////////////////////////////////
   // First level INPUTS
   //////////////////////////////////////////////
   //
   //
   // These signals should be viewed as correlating to the input values pulled 
   // from waves but we choose in this case to use random generated values
   // along with some environment modeling for tags to keep the inputs "legal":
   
   always@* begin
      // src:
      src_cmd_val0    = |rand_src_cmd_val[1:0]; // just increasing freq of valid
      src_is_read0    = rand_src_is_read;
      src_tag0        = next_src_tag;
      src_addr0       = rand_src_addr;
      src_data0       = rand_src_data;
      // dest:
      dest_resp_val0  = rand_dest_resp_val;
      dest_resp_tag0  = next_dest_tag;
      dest_resp_data0 = rand_dest_resp_data;
   end

   //////////////////////////////////////////////
   // Input Transform#1: Address value selection:
   //////////////////////////////////////////////
   //
   //
   // We will take the first address for a valid transaction we see
   // as our focal address and after that, we will use a single free
   // bit to select that address or pass the rand address through.

   always@(posedge clk) begin
      focal_addr_picked <= ~reset & (src_cmd_val0 | focal_addr_picked);
      if (reset) 
        focal_addr <= 0;
      else if (~focal_addr_picked & src_cmd_val0)
        focal_addr <= src_addr0;
   end

   always@*
     pick_src_addr = (focal_addr_picked & free_addr_select) ? focal_addr : src_addr0;
   
   // bind the signals for the output of the first transform:
   always@* begin
      // src:
      src_cmd_val1    = src_cmd_val0;
      src_is_read1    = src_is_read0;
      src_tag1        = src_tag0;
      src_addr1       = pick_src_addr;
      src_data1       = src_data0;
      // dest:
      dest_resp_val1  = dest_resp_val0;
      dest_resp_tag1  = dest_resp_tag0;
      dest_resp_data1 = dest_resp_data0;
   end

   //////////////////////////////////////////////
   // Input Transform#2: Creating bursts:
   //////////////////////////////////////////////
   //
   //
   // The next transform we will apply is simply the generation
   // of "bursts" and in this case, just burts of reads or writes
   // and simply a free variable to change the command to match
   // the last valid command
   
   always@(posedge clk)
     if (reset)
       last_valid_is_read <= 1'b0;
     else if (src_cmd_val)
       last_valid_is_read <= src_is_read;
   
   always@*
     pick_src_cmd = (free_burst_select) ? last_valid_is_read : src_is_read1;
   
   // bind the signals for the output of the second transform:
   always@* begin
      // src:
      src_cmd_val2    = src_cmd_val1;
      src_is_read2    = pick_src_cmd;
      src_tag2        = src_tag1;
      src_addr2       = src_addr1;
      src_data2       = src_data1;
      // dest:
      dest_resp_val2  = dest_resp_val1;
      dest_resp_tag2  = dest_resp_tag1;
      dest_resp_data2 = dest_resp_data1;
   end

   //////////////////////////////////////////////
   // Input Transform#3: Delay injection:
   //////////////////////////////////////////////
   //
   //
   // The final transform. We will store the outgoing command/response
   // and decide to delay it. We only have a size1 buffer, so delays
   // are not possible if we have one in storage and one coming in..
   // Not a bad idea to add more storage in general, but for purely
   // random input, not a big deal..

   // src:
   always@(posedge clk) begin
      if (reset | release_src) begin
         src_hold <= 1'b0;
      end
      else if (hold_new_src) begin
         src_hold <= 1'b1;
         src_cmd_val_h <= src_cmd_val2;
         src_is_read_h <= src_is_read2;
         src_tag_h <= src_tag2;
         src_addr_h <= src_addr2;
         src_data_h <= src_data2;
      end
    end

   always@* begin
      hold_new_src  = (src_hold ? src_cmd_val2 : free_src_delay);
      release_src   = (src_hold & ~src_cmd_val2 & ~free_src_delay);
      pick_src_hold = (src_hold & (src_cmd_val2 | ~free_src_delay));
   end

   always@*
     if (pick_src_hold) begin
        src_cmd_val_d  = src_cmd_val_h;
        src_is_read_d  = src_is_read_h;
        src_tag_d      = src_tag_h;
        src_addr_d     = src_addr_h;
        src_data_d     = src_data_h;
     end else begin
        src_cmd_val_d  = src_cmd_val2;
        src_is_read_d  = src_is_read2;
        src_tag_d      = src_tag2;
        src_addr_d     = src_addr2;
        src_data_d     = src_data2;
     end

   // dest:
   always@(posedge clk) begin
      if (reset | release_dest) begin
         dest_hold <= 1'b0;
      end
      else if (hold_new_dest) begin
         dest_hold <= 1'b1;
         dest_resp_val_h  <= dest_resp_val2;
         dest_resp_tag_h  <= dest_resp_tag2;
         dest_resp_data_h <= dest_resp_data2;
      end
    end

   always@* begin
      hold_new_dest  = (dest_hold ? dest_resp_val2 : free_dest_delay);
      release_dest   = (dest_hold & ~dest_resp_val2 & ~free_dest_delay);
      pick_dest_hold = (dest_hold & (dest_resp_val2 | ~free_dest_delay));
   end

   always@*
     if (pick_dest_hold) begin
        dest_resp_val_d  = dest_resp_val_h;
        dest_resp_tag_d  = dest_resp_tag_h;
        dest_resp_data_d = dest_resp_data_h;
     end else begin
        dest_resp_val_d  = dest_resp_val2;
        dest_resp_tag_d  = dest_resp_tag2;
        dest_resp_data_d = dest_resp_data2;
     end
   
   // bind the signals for the output of the final transform:
   always@* begin
      // src:
      src_cmd_val3    = src_cmd_val_d;
      src_is_read3    = src_is_read_d;
      src_tag3        = src_tag_d;
      src_addr3       = src_addr_d;
      src_data3       = src_data_d;
      // dest:
      dest_resp_val3  = dest_resp_val_d;
      dest_resp_tag3  = dest_resp_tag_d;
      dest_resp_data3 = dest_resp_data_d;
   end


   //////////////////////////////////////////////
   // Final INPUT binding:
   //////////////////////////////////////////////
   //
   //
   // Now bind the final set of inputs to the output of the last transforms:

   always@* begin
      // src:
      src_cmd_val    = src_cmd_val3;
      src_is_read    = src_is_read3;
      src_tag        = src_tag3;
      src_addr       = src_addr3;
      src_data       = src_data3;
      // dest:
      dest_resp_val  = dest_resp_val3;
      dest_resp_tag  = dest_resp_tag3;
      dest_resp_data = dest_resp_data3;
   end

   

   //////////////////////////////////////////////
   // Instantiate the SMQ design:
   //////////////////////////////////////////////
   //
   //
   // instantiate the design:

   smq des(.*);


   
   //////////////////////////////////////////////
   // Build the check for catching deadlock:
   //////////////////////////////////////////////
   //
   //
   // fail_out signal we are checking..
   // ..simply looking for any state where we have some number of reads/writes
   // ..all in STATE_REQ (i.e. waiting to be sent on dest interface) and
   // ..not waiting for any others in other states (e.g. waiting for a response)

   always@(posedge clk) 
     fail_out <= ((|(des.rwq_val & des.rwq_state_req)) & // something in REQ state
                  ~|(des.rwq_val & ~des.rwq_state_req) & // and ALL in REQ state
                  ~|(des.rwq_state_done_d1)            & // 1-clock delay from rwq_val change to older update.
                  ~|(des.entry_rdy));                    // and no one is ready!

endmodule // smq

