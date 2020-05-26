// Your code

module CHIP(clk,
            rst_n,
            // For mem_D
            mem_wen_D,
            mem_addr_D,
            mem_wdata_D,
            mem_rdata_D,
            // For mem_I
            mem_addr_I,
            mem_rdata_I);

    input         clk, rst_n ;
    // For mem_D
    output        mem_wen_D  ;
    output [31:0] mem_addr_D ;
    output [31:0] mem_wdata_D;
    input  [31:0] mem_rdata_D;
    // For mem_I
    output [31:0] mem_addr_I ;
    input  [31:0] mem_rdata_I;
    
    //---------------------------------------//
    // Do not modify this part!!!            //
    // Exception: You may change wire to reg //
    reg    [31:0] PC          ;              //
    wire   [31:0] PC_nxt      ;              //
    wire          regWrite    ;              //
    wire   [ 4:0] rs1, rs2, rd;              //
    wire   [31:0] rs1_data    ;              //
    wire   [31:0] rs2_data    ;              //
    wire   [31:0] rd_data     ;              //
    //---------------------------------------//

    //---------------------------------------//
    // Do not modify this part!!!            //
    reg_file reg0(                           //
        .clk(clk),                           //
        .rst_n(rst_n),                       //
        .wen(regWrite),                      //
        .a1(rs1),                            //
        .a2(rs2),                            //
        .aw(rd),                             //
        .d(rd_data),                         //
        .q1(rs1_data),                       //
        .q2(rs2_data));                      //
    //---------------------------------------//

	// ===== params =====
	localparam OP_LW = 		7'b0000011;
	localparam OP_ADDI =	7'b0010011;
	localparam OP_SLTI = 	7'b0010011;
	localparam OP_SLLI = 	7'b0010011;
	localparam OP_SRAI = 	7'b0010011;
	localparam OP_AUIPC =	7'b0010111;
	localparam OP_SW =		7'b0100011;
	localparam OP_ADD =		7'b0110011;
	localparam OP_SUB =		7'b0110011;
	localparam OP_MUL =		7'b0110011;
	localparam OP_BEQ =		7'b1100011;
	localparam OP_JALR =	7'b1100111;
	localparam OP_JAL =		7'b1101111;

    // ===== variables =========

	wire [31:0] ins;
	assign ins = mem_rdata_I;

    // pc

    // control unit
    wire 			ctrl_beq, ctrl_jal, ctrl_jalr;	// for pc nxt, set the 1 for the according instruction
	wire [2:0]		ctrl_regSrc;	// reg write back (there're six sources)
	wire [1:0]		ctrl_aluOp;		//
	wire [1:0]		ctrl_aluSrc;	// for input A and B, 0: rs_data, 1: special case
	wire 			ctrl_mulValid;

    // ImmGen
    wire [31:0]     immGen_res;     // not shifted for pc jump (in current design)

    // ALU
	wire [31:0]		alu_A, alu_B;
    wire [31:0]     alu_res;
    wire            alu_zero;

    // Shift
	wire [31:0]		shift_res

    // MulDiv
    wire [31:0]     mul_res;
    wire            mul_done;


    // ===== output assignments =======
    assign mem_addr_I = PC;
	assign mem_addr_D = alu_res;
	assign mem_wdata_D = rs2_data;
	// assign mem_wen_D =
	// ================================
    

    // Todo: PC logics
    wire [31:0]     pc_jump;
	wire			pc_jump_sel;

    assign pc_jump = pc + {immGen_res[30:0], 1'b0};
	assign pc_jump_sel = ctrl_jal | ( ctrl_beq & alu_zero )
    assign PC_nxt = ctrl_jalr ? alu_res : ( pc_jump_sel ? pc_jump : ( mul_done ? PC : PC + 32'd4 )  );

    // Todo: Control Unit
    always @(*) begin
		mem_wen_D = 1'b0;
		ctrl_regSrc = 3'b000;
		ctrl_aluOp = 2'b00;
		ctrl_aluSrc = 2'b00;
		regWrite = 0;

		case ( ins[6:0] )

			// ADD
			OP_ADD: begin
				ctrl_aluOp = 2'b10;
				regWrite = 1'b1;
			end

			// ADDI
			OP_ADDI: begin
				ctrl_aluSrc = 2'b01;
				regWrite = 1'b1;
			end

			// AUIPC
			OP_AUIPC: begin
				ctrl_aluSrc = 2'b11;
				regWrite = 1'b1;
			end

			// BEQ
			OP_BEQ: ctrl_aluOp = 2'b01;

			// JAL
			// default values

			// JALR
			OP_JALR: ctrl_aluSrc = 2'b01;

			// LW
			OP_LW: begin
				ctrl_regSrc = 3'b011;
				ctrl_aluSrc = 2'b01;
				regWrite = 1'b1;
			end

			// MUL
			OP_MUL: begin
				ctrl_regSrc = 3'b010;
				regWrite = 1'b1;
			end

			// SLLI
			OP_SLLI: begin
				ctrl_regSrc = 3'b101;
				regWrite = 1'b1;
			end
			
			// SLTI
			OP_SLTI: begin
				ctrl_regSrc = 3'b001;
				ctrl_aluOp = 2'b01;
				ctrl_aluSrc = 2'b01;
				regWrite = 1'b1;
			end

			// SRAI
			OP_SRAI: begin
				ctrl_regSrc = 3'b101;
				regWrite = 1'b1;
			end

			// SUB
			OP_SUB: begin
				ctrl_aluOp = 2'b10;
				regWrite = 1'b1;
			end

			// SW
			OP_SW: begin
				mem_wen_D = 1'b1;
				ctrl_aluSrc = 2'b01;
			end

		endcase
        
    end

    // Todo: ImmGen
    always @(*) begin
		case( ins[6:0] )
			OP_AUIPC:	immGen_res = {ins[31:12], 12'b0};
			OP_JAL:		immGen_res = { {11{ins[31]}}, ins[31], ins[19:12], ins[20], ins[30:21], 1'b0};
			OP_SW:		immGen_res = { {20{ins[31]}}, ins[31:25], ins[11:7] };
			OP_BEQ:		immGen_res = { {19{ins[31}}, ins[31], ins[7], ins[30:25], ins[11:8], 1'b0 };
			OP_ADDI, OP_SLTI, OP_LW, OP_JALR: immGen_res = { {20{ins[31]}}, ins[31:20] };
			default:	immGen_res = '0;
		endcase
    end

    // Todo: ALU
	assign alu_A = ctrl_aluSrc[1] ? PC : rs1_data;
	assign alu_B = ctrl_aluSrc[0] ? immGen_res : rs2_data;
    always @(*) begin
        
	end

    // Todo: Shift
	wire [4:0] shift_amt;
	assign shift_amt = ins[24:20];
	wire [93:0] shift_tmp;
	assign shift_tmp = { {31{rs1_data[31]}}, rs1_data, 31'b0 };
	assign shift_res = ins[30] ? shift_tmp[(62+shift_amt) -: 32] : shift_tmp[(62-shift_amt) -: 32];

    // Todo: mul
	multDiv mul(
		.clk(clk),
		.rst_n(rst_n),
		.valid(ctrl_mulValid),
		.ready(mul_done),
		.mode(1'b0),
		.in_A(rs1_data),
		.in_B(rs2_data),
		.out(mul_res)
	);

	// Todo: reg (write back)




    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            PC <= 32'h00010000; // Do not modify this value!!!
            
        end
        else begin
            PC <= PC_nxt;
            
        end
    end
endmodule

module reg_file(clk, rst_n, wen, a1, a2, aw, d, q1, q2);
   
    parameter BITS = 32;
    parameter word_depth = 32;
    parameter addr_width = 5; // 2^addr_width >= word_depth
    
    input clk, rst_n, wen; // wen: 0:read | 1:write
    input [BITS-1:0] d;
    input [addr_width-1:0] a1, a2, aw;

    output [BITS-1:0] q1, q2;

    reg [BITS-1:0] mem [0:word_depth-1];
    reg [BITS-1:0] mem_nxt [0:word_depth-1];

    integer i;

    assign q1 = mem[a1];
    assign q2 = mem[a2];

    always @(*) begin
        for (i=0; i<word_depth; i=i+1)
            mem_nxt[i] = (wen && (aw == i)) ? d : mem[i];
    end

    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            mem[0] <= 0;
            for (i=1; i<word_depth; i=i+1) begin
                case(i)
                    32'd2: mem[i] <= 32'hbffffff0;
                    32'd3: mem[i] <= 32'h10008000;
                    default: mem[i] <= 32'h0;
                endcase
            end
        end
        else begin
            mem[0] <= 0;
            for (i=1; i<word_depth; i=i+1)
                mem[i] <= mem_nxt[i];
        end       
    end
endmodule

module multDiv(clk, rst_n, valid, ready, mode, in_A, in_B, out);

    // Definition of ports
    input         clk, rst_n;
    input         valid, mode; // mode: 0: multu, 1: divu
    input  [31:0] in_A, in_B;
    output [63:0] out;
    output ready;

    // Definition of states
    parameter S_IDLE = 2'b00;
    parameter S_MULT = 2'b01;
    parameter S_DIVI = 2'b10;
    parameter S_DONE = 2'b11;

    // Todo: Wire and reg
    reg  [ 1:0] state_r, state_w;
    reg  [ 4:0] cnt_r, cnt_w;
    reg  [63:0] shreg_r, shreg_w;
    reg  [31:0] alu_in_r, alu_in_w;
    wire  [32:0] alu_out;

    // Todo 5: wire assignments
    assign out = (state_r == S_DONE) ? shreg_r : 64'b0;
    assign ready = (state_r == S_MULT || start_r == DIVI) ? 1'b0 : 1'b1;
    
    // Combinational always block
    // State machine & counter
    always @(*) begin
        state_w = state_r;
        cnt_w = cnt_r;
        case(state_r)
            S_IDLE: begin
                if (valid) begin
                    state_w = mode ? S_DIVI : S_MULT;
                    cnt_w = 31;
                end
            end
            S_MULT, S_DIVI: begin
                state_w = (cnt_r == 0) ? S_DONE : state_w;
                cnt_w = (cnt_r == 0) ? cnt_w : cnt_r - 1;
            end
            S_DONE: state_w = S_IDLE;
        endcase
    end
    
    // ALU input
    always @(*) begin
        alu_in_w = alu_in_r;
        case(state_r)
            S_IDLE: begin
                if (valid) alu_in_w = in_B;
            end
            S_DONE: alu_in_w = 0;
        endcase
    end
    // ALU output
    assign alu_out = (state_r == S_MULT) ? shreg_r[63:32] + alu_in_r : shreg_r[62:31] - alu_in_r;
    
    // Shift register
    always @(*) begin
        shreg_w = shreg_r;
        case(state_r)
            S_IDLE: if (valid) shreg_w = mode ? {32'b0, in_A} : {32'b0, in_A};
            S_MULT: shreg_w = shreg_r[0] ? {alu_out, shreg_r[31:1]} : (shreg_r >> 1);
            S_DIVI: shreg_w = alu_out[32] ?  (shreg_r << 1) : {alu_out[31:0], shreg_r[30:0], 1'b1};
        endcase
    end

    // Sequential always block
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state_r <= S_IDLE;
            cnt_r <= 0;
            shreg_r <= 0;
            alu_in_r <= 0;
        end
        else begin
            state_r <= state_w;
            cnt_r <= cnt_w;
            shreg_r <= shreg_w;
            alu_in_r <= alu_in_w;
        end
    end

endmodule
