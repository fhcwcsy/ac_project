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
    reg          regWrite    ;              //
    wire   [ 4:0] rs1, rs2, rd;              //
    wire   [31:0] rs1_data    ;              //
    wire   [31:0] rs2_data    ;              //
    reg   [31:0] rd_data     ;              //
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
	localparam OP_I_TYPE = 	7'b0010011;
	localparam OP_AUIPC =	7'b0010111;
	localparam OP_SW =		7'b0100011;
	localparam OP_R_TYPE =	7'b0110011;
	localparam OP_BEQ =		7'b1100011;
	localparam OP_JALR =	7'b1100111;
	localparam OP_JAL =		7'b1101111;

    // ===== variables =========

	wire [31:0] ins;
	assign ins = mem_rdata_I;

    // pc

    // control unit
    reg 			ctrl_beq, ctrl_jal, ctrl_jalr;	// for pc nxt, set the 1 for the according instruction
	reg [1:0]		ctrl_regSrc;	// reg write back (there're six sources)
	reg [1:0]		ctrl_aluOp;		//
	reg [1:0]		ctrl_aluSrc;	// for input A and B, 0: rs_data, 1: special case
	reg 			ctrl_mulValid;
	reg			ctrl_mem_wen_D;

    // ImmGen
    reg [31:0]     immGen_res;     // not shifted for pc jump (in current design)

    // ALU
	wire [31:0]		alu_A, alu_B;
    reg [31:0]     alu_out;
    wire            alu_zero;
	reg [2:0]		alu_input;
	reg [31:0]		alu_regSrc;

    // Shift
	wire [31:0]		shift_res;

    // MulDiv
    wire [31:0]     mul_res;
    wire            mul_done;


    // ===== output assignments =======
    assign mem_addr_I = PC;
	assign mem_addr_D = alu_out;
	assign mem_wdata_D = rs2_data;
	assign mem_wen_D = ctrl_mem_wen_D;
	// ================================
    

    // Todo: PC logics
    wire [31:0]     pc_jump;
	wire			pc_jump_sel;

    assign pc_jump = PC + immGen_res;
	assign pc_jump_sel = ctrl_jal | ( ctrl_beq & alu_zero );
    assign PC_nxt = ctrl_jalr ? alu_out : ( pc_jump_sel ? pc_jump : ( mul_done ? PC + 32'd4 : PC )  );

    // Control Unit
	localparam RegSrc_ALU = 2'b00;
	localparam RegSrc_PC_4 = 2'b01;
	localparam RegSrc_Mem = 2'b10;

    always @(*) begin
		ctrl_mem_wen_D = 1'b0;
		ctrl_regSrc = 3'b000;
		ctrl_aluOp = 2'b00;
		ctrl_aluSrc = 2'b00;
		regWrite = 1'b0;
		ctrl_beq = 1'b0;
		ctrl_jal = 1'b0;
		ctrl_jalr = 1'b0;

		case ( ins[6:0] )

			// R-TYPE
			OP_R_TYPE: begin
				ctrl_aluOp = 2'b10;
				regWrite = 1'b1;
			end

			// I-TYPE
			OP_I_TYPE: begin
				ctrl_aluOp = 2'b11;
				ctrl_aluSrc = 2'b01;
				regWrite = 1'b1;
			end

			// AUIPC
			OP_AUIPC: begin
				ctrl_aluSrc = 2'b11;
				regWrite = 1'b1;
			end

			// BEQ
			OP_BEQ: begin
				ctrl_aluOp = 2'b01;
				ctrl_beq = 1'b1;
			end

			// JAL
			OP_JAL: begin
				ctrl_jal = 1'b1;
				regWrite = 1'b1;
				ctrl_regSrc = RegSrc_PC_4;	// debug
			end

			// JALR
			OP_JALR: begin
				ctrl_aluSrc = 2'b01;
				ctrl_jalr = 1'b1;
				regWrite = 1'b1;
				ctrl_regSrc = RegSrc_PC_4;	// debug
			end

			// LW
			OP_LW: begin
				ctrl_regSrc = RegSrc_Mem;
				ctrl_aluSrc = 2'b01;
				regWrite = 1'b1;
			end

			// SW
			OP_SW: begin
				ctrl_mem_wen_D = 1'b1;
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
			OP_BEQ:		immGen_res = { {19{ins[31]}}, ins[31], ins[7], ins[30:25], ins[11:8], 1'b0 };
			OP_I_TYPE, OP_JALR, OP_LW: immGen_res = { {20{ins[31]}}, ins[31:20] };
			default:	immGen_res = 32'b0;
		endcase
    end
	
	// ALU control
	always @(*) begin

		// Default: 
		// ALU: addition
		// multiplier: pause
		alu_input = 3'b010;
		ctrl_mulValid = 1'b0;
		alu_regSrc = alu_out;

		case ( ctrl_aluOp )

			// Always subtract
			2'b01: alu_input = 3'b110;

			// R type
			2'b10: begin
				case ( ins[31:25] )

					// Addition: defined in default values

					// Multiplication
					7'b0000001: begin
						ctrl_mulValid = 1'b1;
						alu_regSrc = mul_res;				// debug
					end

					// Subtraction
					7'b0100000: alu_input = 3'b110;

				endcase
			end

			// I type
			2'b11: begin
				case ( ins[14:12] )
					// SLLI, SRAI
					3'b001, 3'b101: alu_regSrc = shift_res; 

					// SLTI
					3'b010: begin
						alu_regSrc = {31'b0, alu_out[31]};
						alu_input = 3'b110;
					end

					// ADDI
					// default values
				endcase
			end
		endcase
	end

	// ALU

	// ALU input
	assign alu_A = ctrl_aluSrc[1] ? PC : rs1_data;
	assign alu_B = ctrl_aluSrc[0] ? immGen_res : rs2_data;
	assign alu_zero = alu_out ? 0 : 1;
	
	// AlU output
	always @(*) begin
		case (alu_input)

			// Addition
			3'b010: alu_out = alu_A + alu_B;

			// Subtraction
			3'b110: alu_out = alu_A - alu_B;

			// default output: 0
			default:
				alu_out = 32'b0;

		endcase
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

	// Todo: reg
	assign rs1 = ins[19:15];
	assign rs2 = ins[24:20];
	assign rd = ins[11:7];

	always @(*) begin
		case(ctrl_regSrc)
			default: rd_data = 32'b0;
			RegSrc_ALU: rd_data = alu_regSrc;
			RegSrc_PC_4: rd_data = PC + 4;
			RegSrc_Mem: rd_data = mem_rdata_D;
		endcase
	end




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
    assign ready = ( valid && state_r != S_DONE ) ? 1'b0 : 1'b1;
    
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
