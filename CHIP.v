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

    //reg [31:0] mem_addr_I ;
    reg [31:0] mem_addr_D ;
    reg [31:0] mem_wdata_D;
    
    //---------------------------------------//
    // Do not modify this part!!!            //
    // Exception: You may change wire to reg //
    reg    [31:0] PC          ;              //
    reg   [31:0] PC_nxt      ;              //
    wire          regWrite    ;              //
    reg   [ 4:0] rs1, rs2, rd;              //
    wire   [31:0] rs1_data    ;              //
    wire   [31:0] rs2_data    ;              //
    reg   [31:0] rd_data     ;              //
    //---------------------------------------//
    wire regWrite0;

    // Every constant
    parameter RTYPE = 7'b0110011;
    parameter ITYPE  = 7'b00x0011;
    parameter STYPE  = 7'b0100011;
    parameter BTYPE = 7'b1100011;
    parameter UTYPE  = 7'b0x10111;
    parameter JTYPE = 7'b110x111;

    parameter IF = 3'b000;
    parameter ID = 3'b001;
    parameter EX = 3'b010;
    parameter ME = 3'b011;
    parameter WB = 3'b100;

    parameter MUL = 3'b000;
    parameter LT = 3'b001;
    parameter ADD = 3'b010;
    parameter SUB = 3'b011;
    parameter XOR = 3'b100;
    parameter SHIFT_R = 3'b101;
    parameter SHIFT_L = 3'b110;
    parameter NOT_USED = 3'b111;
    

    // Todo: other wire/reg
    wire Branch;
    wire MemRead;
    wire MemToReg;
    wire MemWrite;
    wire ALUSrc;

    wire write_en;

    wire jal;
    wire jalr;
    wire auipc;

    reg [31:0] imm_gen;

    reg [1:0] ALUOp;
    wire [2:0] alu_mode ;

    reg [31:0] alu_out ;
    wire [31:0] mulDiv_out ;
    reg [31:0] mulDiv_out_save;

    reg [5:0] alu_valid_counter;
    reg [5:0] alu_valid_counter_nxt;
    reg alu_valid ;

    reg alu_ready ;
    wire mulDiv_ready ;
    wire ready ;

    reg Branch_Succeed ;

    reg [2:0] state;
    reg [2:0] state_nxt;

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
        .q2(rs2_data)
    );                                       //
    //---------------------------------------//

    control control01(
        .instruction(mem_rdata_I[6:0]),
        .Branch(Branch),
        .MemRead(MemRead),
        .MemToReg(MemToReg),
        .MemWrite(MemWrite),
        .ALUSrc(ALUSrc),
        .jal(jal),
        .jalr(jalr),
        .auipc(auipc),
        .regWrite(regWrite0)
    );
    assign regWrite = regWrite0 && (state == WB);

    ALUcontrol ALUcontrol01(
        .opcode(mem_rdata_I[6:0]),
        .ALUOp(ALUOp),
        .funct3(mem_rdata_I[14:12]),
        .funct7(mem_rdata_I[31:25]),
        .alu_mode(alu_mode)
    ) ;

    // Todo: any combinational/sequential circuit
    //FSM
    always @(*) begin 
        case(state) 
            IF : state_nxt = ID;
            ID : state_nxt = EX;
            EX : begin
                if(alu_mode == MUL) begin
                    state_nxt = (mulDiv_ready)? ME : EX;
                end
                else state_nxt = ME;
            end
            ME : state_nxt = WB;
            WB : state_nxt = IF;
            default : state_nxt = IF;
        endcase
    end

    //take branch?
    always @(*) begin
        if(state == WB) begin
            if(mem_rdata_I[14:12] == 3'b000) Branch_Succeed = (alu_out == 0)? 1 : 0;
            else Branch_Succeed = ($signed(alu_out) >= 0)? 1 : 0; 
        end
        else Branch_Succeed = 0;
    end
    //PC
    always @(*) begin
        PC_nxt = PC;
        if(state == WB) begin
            if(Branch && Branch_Succeed) PC_nxt = PC + $signed(imm_gen << 1);
            else if(jal) PC_nxt = PC + $signed(imm_gen << 1);
            else if(jalr) PC_nxt = alu_out;
            else PC_nxt = PC + 32'd4; 
        end
    end
    
    //IF
    assign mem_addr_I = PC;

    //ID
    always @(*) begin
        rs1 = rs1;
        rs2 = rs2;
        rd = rd;
        imm_gen = imm_gen;
        ALUOp = ALUOp;
        if(state == ID) begin
            casex (mem_rdata_I[6:0])
                RTYPE: begin
                    rs1 = mem_rdata_I[19:15];
                    rs2 = mem_rdata_I[24:20];
                    rd = mem_rdata_I[11:7];
                    imm_gen = 0;
                    ALUOp = 2'b00;
                end
                ITYPE: begin
                    rs1 = mem_rdata_I[19:15];
                    rs2 = 0;
                    rd = mem_rdata_I[11:7];
                    imm_gen[11:0] = mem_rdata_I[31:20];
                    imm_gen = {{20{imm_gen[11]}}, imm_gen[11:0]};
                    ALUOp = 2'b01;
                end 
                STYPE: begin
                    rs1 = mem_rdata_I[19:15];
                    rs2 = mem_rdata_I[24:20];
                    rd=0;
                    imm_gen[4:0] = mem_rdata_I[11:7];
                    imm_gen[11:5] = mem_rdata_I[31:25];
                    imm_gen = {{20{imm_gen[11]}}, imm_gen[11:0]};
                    ALUOp = 2'b10;
                end
                BTYPE: begin
                    rs1 = mem_rdata_I[19:15];
                    rs2 = mem_rdata_I[24:20];
                    rd = 0;
                    imm_gen[3:0] = mem_rdata_I[11:8];
                    imm_gen[10] = mem_rdata_I[7];
                    imm_gen[9:4] = mem_rdata_I[30:25];
                    imm_gen[11] = mem_rdata_I[31];
                    imm_gen = {{20{imm_gen[11]}}, imm_gen[11:0]};
                    ALUOp = 2'b10;
                end
                UTYPE:  begin
                    rs1 = 0;
                    rs2 =0;
                    rd = mem_rdata_I[11:7];
                    imm_gen[31:12] = mem_rdata_I[31:12];
                    imm_gen[11:0] = 0;
                    ALUOp = 2'b11;
                end
                JTYPE:  begin
                    rs2 = 0;
                    rd = mem_rdata_I[11:7];
                    if (mem_rdata_I[3] == 0) begin
                        rs1 = mem_rdata_I[19:15];
                        imm_gen[11:0] = mem_rdata_I[31:20];
                        imm_gen = {{20{imm_gen[11]}}, imm_gen[11:0]}; 
                    end
                    else begin
                        rs1=0;
                        imm_gen[18:11] = mem_rdata_I[19:12];
                        imm_gen[10] = mem_rdata_I[20];
                        imm_gen[9:0] = mem_rdata_I[30:21];
                        imm_gen[19] = mem_rdata_I[31];
                        imm_gen = {{12{imm_gen[19]}}, imm_gen[19:0]};
                    end
                    ALUOp = 2'b11;
                end
                default: begin
                    rs1 = 0;
                    rs2 = 0;
                    rd = 0;
                    imm_gen = 0;
                    ALUOp = 2'b10;
                end
            endcase
        end
    end

    //EX
    always @(*) begin
        if(state == EX) begin
            alu_valid_counter_nxt = alu_valid_counter + 1;
        end
        else begin
            alu_valid_counter_nxt = 0;
        end
    end
    always @(*) begin
        if(state == EX && alu_valid_counter == 0) begin
            alu_valid = 1;
        end
        else begin
            alu_valid = 0;
        end
    end

    mulDiv mulDiv01(.clk(clk), 
                    .rst_n(rst_n), 
                    .valid(alu_valid && alu_mode == MUL), 
                    .ready(mulDiv_ready), 
                    .mode(alu_mode[1:0]), 
                    .in_A(rs1_data), 
                    .in_B((ALUSrc) ? imm_gen : rs2_data), 
                    .out(mulDiv_out));
    always @(*) begin
        mulDiv_out_save = mulDiv_out_save;
        if(state == EX) mulDiv_out_save = mulDiv_out;
    end

    always @(*) begin
        alu_out = alu_out;
        if(state == EX) begin
            case(alu_mode)
                ADD : begin
                    if (ALUSrc == 1) alu_out = rs1_data + imm_gen; 
                    else alu_out = rs1_data + rs2_data; 
                end
                LT:  begin
                    if (ALUSrc == 1) alu_out = ($signed(rs1_data) < $signed(imm_gen)); 
                    else alu_out = ($signed(rs1_data) < $signed(rs2_data)); 
                end
                SUB : begin
                    if (ALUSrc == 1) alu_out = rs1_data - imm_gen; 
                    else alu_out = rs1_data - rs2_data; 
                end
                SHIFT_L : begin
                    if (ALUSrc == 1) alu_out = rs1_data << imm_gen; 
                    else alu_out = rs1_data << rs2_data; 
                end
                SHIFT_R : begin
                    if (ALUSrc == 1) alu_out = rs1_data >> imm_gen; 
                    else alu_out = rs1_data >> rs2_data; 
                end
                XOR : begin
                    if (ALUSrc == 1) alu_out = rs1_data ^ imm_gen; 
                    else alu_out = rs1_data ^ rs2_data; 
                end
                default : begin
                    alu_out = 0;
                end
            endcase
        end
    end 

    //ME
    assign write_en = MemWrite && (state == ME);

    assign mem_wen_D = write_en;

    always @(*) begin
        mem_addr_D = mem_addr_D;
        mem_wdata_D = mem_wdata_D;
        if(state == ME) begin
            mem_addr_D = alu_out;
            mem_wdata_D = rs2_data;
        end
    end

    //WB
    always @(*) begin
        rd_data = rd_data;
        if(state == WB) begin
            if(jal) rd_data = PC + 3'd4;
            else if(jalr) rd_data = PC + 3'd4;
            else if(auipc) rd_data = PC + (imm_gen << 12);
            else begin
                if(MemToReg == 1) begin
                    rd_data = mem_rdata_D;
                end
                else begin
                    rd_data = (alu_mode == MUL)? mulDiv_out_save : alu_out;
                end
            end
        end
    end


    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            PC <= 32'h00010000; // Do not modify this value!!!
            state <= IF;
            alu_valid_counter <= 0;
        end
        else begin
            PC <= PC_nxt;
            state <= state_nxt;
            alu_valid_counter <= alu_valid_counter_nxt;
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

module ALUcontrol (opcode, funct3, funct7, ALUOp, alu_mode);
    parameter MUL = 3'b000;
    parameter LT = 3'b001;
    parameter ADD = 3'b010;
    parameter SUB = 3'b011;
    parameter XOR = 3'b100;
    parameter SHIFT_R = 3'b101;
    parameter SHIFT_L = 3'b110;
    parameter NOT_USED = 3'b111;
    parameter R = 2'b00;
    parameter I = 2'b01;
    parameter BS = 2'b10;
    parameter UJ = 2'b11;
    

    input [6:0] opcode;
    input [2:0] funct3;
    input [6:0] funct7;
    input [1:0] ALUOp;
    output [2:0] alu_mode;
    reg [2:0] alu_mode;

    always @(*) begin
        alu_mode = NOT_USED;
        case (ALUOp)
            R:begin 
                if (funct3 == 3'b100) alu_mode = XOR;
                else if (funct3 == 3'b000) begin
                    if (funct7[5] == 1) alu_mode = SUB;
                    else if(funct7[0] == 1) alu_mode = MUL;
                    else alu_mode = ADD;
                end
            end 
            I: begin 
                if(funct3 == 3'b101) alu_mode = SHIFT_R;
                else if(funct3 == 3'b001) alu_mode = SHIFT_L;
                else if(funct3 == 3'b010 && opcode[4] == 1) alu_mode = LT;
                else alu_mode = ADD;
            end
            BS: begin
                if((funct3 == 3'b000) || (funct3 == 3'b101)) alu_mode = SUB;
                else alu_mode = ADD;
            end
            UJ: begin
                if(opcode[6:0] == 7'b1101111) alu_mode = NOT_USED;
                else alu_mode = ADD;
            end
        endcase
    end
endmodule

module mulDiv(clk, rst_n, valid, ready, mode, in_A, in_B, out);
    // Definition of ports
    input         clk, rst_n;
    input         valid;
    input  [1:0]  mode; // mode: 0: mulu, 1: divu, 2: and, 3: avg
    output        ready;
    input  [31:0] in_A, in_B;
    output [31:0] out;
    
    // Definition of states
    parameter IDLE = 3'd0;
    parameter MUL  = 3'd1;
    parameter DIV  = 3'd2;
    parameter AND = 3'd3;
    parameter AVG = 3'd4;
    parameter OUT  = 3'd5;

    // Todo: Wire and reg if needed
    reg  [ 2:0] state, state_nxt;
    reg  [ 4:0] counter, counter_nxt;
    reg  [63:0] shreg, shreg_nxt;
    reg  [31:0] alu_in, alu_in_nxt;
    reg  [32:0] alu_out;

    // Todo: Instatiate any primitives if needed

    // Todo 5: Wire assignments
    assign out = shreg[31:0];
    assign ready = (state == OUT);
    // Combinational always block
    // Todo 1: Next-state logic of state machine
    always @(*) begin
        case(state)
            IDLE: begin
                if(!valid) begin
                    state_nxt = IDLE;
                end
                else begin  
                    case(mode)
                        2'd0 : state_nxt = MUL;
                        2'd1 : state_nxt = DIV;
                        2'd2 : state_nxt = AND;
                        2'd3 : state_nxt = AVG;
                    endcase
                end     
            end
            MUL : begin
                if(counter == 5'd31) state_nxt = OUT;
                else state_nxt = MUL;
            end
            DIV : begin
                if(counter == 5'd31) state_nxt = OUT;
                else state_nxt = DIV;
            end
            AND : state_nxt = OUT;
            AVG : state_nxt = OUT;
            OUT : state_nxt = IDLE;
            default : state_nxt = IDLE;
        endcase
    end
    // Todo 2: Counter
    always @(*) begin
        case(state)
            MUL : begin
                if(counter == 5'd31)begin
                    counter_nxt = 0;
                end
                else begin
                    counter_nxt = counter + 5'd1;
                end
            end
            DIV : begin
                if(counter == 5'd31)begin
                    counter_nxt = 0;
                end
                else begin
                    counter_nxt = counter + 5'd1;
                end
            end
            default : begin
                counter_nxt = counter;
            end
        endcase
    end
    // ALU input
    always @(*) begin
        case(state)
            IDLE: begin
                if (valid) alu_in_nxt = in_B;
                else       alu_in_nxt = 0;
            end
            OUT : alu_in_nxt = 0;
            default: alu_in_nxt = alu_in;
        endcase
    end

    // Todo 3: ALU output
    always @(*) begin
        case(state)
            IDLE: begin
                alu_out = 0;
            end
            MUL : begin
                if(shreg[0] == 1)begin
                    alu_out = shreg[63:32] + alu_in;
                end     
                else begin
                    alu_out = shreg[63:32];
                end
            end
            DIV : begin
                if(shreg[63:32] - alu_in < shreg[63:32])begin
                    alu_out = shreg[63:32] - alu_in;
                end
                else begin
                    alu_out = shreg[63:32];
                end
            end
            AND : begin 
                alu_out = alu_in & shreg[31:0];
            end
            AVG : alu_out = (alu_in + shreg[31:0]) >> 1;
            OUT : alu_out = 0;
            default : alu_out = 0;
        endcase
    end 
    // Todo 4: Shift register
    always @(*) begin
        case(state)
            IDLE : begin
                if (valid) begin
                    if(mode == 2'd1) begin
                        shreg_nxt[63:0] = {32'd0 , in_A} << 2;
                    end
                    else begin
                        shreg_nxt = {32'd0 , in_A};
                    end
                end
                else    shreg_nxt[63:0] = 0;
            end
            MUL : begin
                shreg_nxt[63:0] = {alu_out , shreg[31:0]} >> 1;
            end
            DIV : begin
                if(counter == 5'd31) begin
                    shreg_nxt[63:0] = {shreg[63:32] >> 1 , shreg[31:0]};
                end 
                else begin
                    if(shreg[63:32] - alu_in >= shreg[63:32])begin
                        shreg_nxt[63:0] =  (shreg[63:0] << 1);
                    end
                    else begin
                        shreg_nxt[63:0] =  ({alu_out[31:0] , shreg[31:0]} << 1) + 64'd1;
                    end
                end
            end
            AND : shreg_nxt[63:0] = {32'd0 , alu_out};
            AVG : shreg_nxt[63:0] = {32'd0 , alu_out};
            OUT : shreg_nxt[63:0] = 0;
            default : shreg_nxt[63:0] = 0;
        endcase
    end

    // Todo: Sequential always block
    always @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            state <= IDLE;
            counter <= 0;
            shreg <= 0;
            alu_in <= 0;
        end
        else begin
            state <= state_nxt;
            counter <= counter_nxt;
            shreg <= shreg_nxt;
            alu_in <= alu_in_nxt;
        end
    end
endmodule

module control(instruction, Branch, MemRead, MemToReg, MemWrite, ALUSrc, jal, jalr, auipc, regWrite);
    input [6:0] instruction;
    output Branch;
    output MemRead;
    output MemToReg;
    output MemWrite;
    output ALUSrc;
    output jal;
    output jalr;
    output auipc;
    output regWrite;

    reg [8:0] Output;

    reg Branch;
    reg MemRead;
    reg MemToReg;
    reg MemWrite;
    reg ALUSrc;
    reg jal;
    reg jalr;
    reg auipc;
    reg regWrite;

    always @(*) begin
        case(instruction)
            7'b0010111 : begin //auipc
                Output = 9'b0000_00011;
            end
            7'b1101111 : begin //jal
                Output = 9'b0000_01001;
            end
            7'b1100111 : begin //jalr
                Output = 9'b0000_10101;
            end
            7'b1100011 : begin //BEQ
                Output = 9'b1000_00000;
            end
            7'b0000011 : begin //lw
                Output = 9'b0110_10001;
            end
            7'b0100011 : begin // sw 
                Output = 9'b0001_10000;
            end
            7'b0010011 : begin // addi,slti
                Output = 9'b0000_10001;
            end
            7'b0110011 : begin //add 
                Output = 9'b0000_00001;
            end
            default : Output = 9'b0000_00000;
        endcase

        Branch = Output[8];
        MemRead = Output[7];
        MemToReg = Output[6];
        MemWrite = Output[5];
        ALUSrc = Output[4];
        jal = Output[3];
        jalr = Output[2];
        auipc = Output[1];
        regWrite = Output[0];
    end
endmodule