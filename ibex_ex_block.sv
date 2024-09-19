// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Execution stage
 *
 * Execution block: Hosts ALU and MUL/DIV unit
 */
`include "prim_assert.sv"
`include "dv_fcov_macros.svh" 

module ibex_ex_block #(
    parameter ResetAll = 1'b0,
  parameter ibex_pkg::rv32m_e RV32M           = ibex_pkg::RV32MFast,
  parameter ibex_pkg::rv32b_e RV32B           = ibex_pkg::RV32BNone,
  parameter bit               BranchTargetALU = 0
) (
  input  logic                  clk_i,
  input  logic                  rst_ni,

  // ALU
  input  ibex_pkg::alu_op_e     alu_operator_i,
  input  logic [31:0]           alu_operand_a_i,
  input  logic [31:0]           alu_operand_b_i,
  input  logic                  alu_instr_first_cycle_i,

  // Branch Target ALU
  // All of these signals are unusued when BranchTargetALU == 0
  input  logic [31:0]           bt_a_operand_i,
  input  logic [31:0]           bt_b_operand_i,

  // Multiplier/Divider
  input  ibex_pkg::md_op_e      multdiv_operator_i,
  input  logic                  mult_en_i,             // dynamic enable signal, for FSM control
  input  logic                  div_en_i,              // dynamic enable signal, for FSM control
  input  logic                  mult_sel_i,            // static decoder output, for data muxes
  input  logic                  div_sel_i,             // static decoder output, for data muxes
  input  logic  [1:0]           multdiv_signed_mode_i,
  input  logic [31:0]           multdiv_operand_a_i,
  input  logic [31:0]           multdiv_operand_b_i,
  input  logic                  multdiv_ready_id_i,
  input  logic                  data_ind_timing_i,

  // intermediate val reg
  output logic [1:0]            imd_val_we_o,
  output logic [33:0]           imd_val_d_o[2],
  input  logic [33:0]           imd_val_q_i[2],

  // Outputs
  output logic [31:0]           alu_adder_result_ex_o, // to LSU
  output logic [31:0]           result_ex_o,
  output logic [31:0]           branch_target_o,       // to IF
  output logic                  branch_decision_o,     // to ID

  output logic                  ex_valid_o,             // EX has valid output

  //to EX_MA pipeline
  input  logic         lsu_we_ex_i,             // write enable                     -> from ID/EX
  input  logic [1:0]   lsu_type_ex_i,           // data type: word, half word, byte -> from ID/EX
  input  logic [31:0]  lsu_wdata_ex_i,          // data to write to memory          -> from ID/EX
  input  logic         lsu_sign_ext_ex_i,       // sign extension      

  output  logic         lsu_we_ma_o,             // write enable                     -> from ID/EX
  output  logic [1:0]   lsu_type_ma_o,           // data type: word, half word, byte -> from ID/EX
  output  logic [31:0]  lsu_wdata_ma_o,          // data to write to memory          -> from ID/EX
  output  logic         lsu_sign_ext_ma_o,       // sign extension   

  //to EX_MA_WB pipeline
  input  logic                     en_wb_ex_i,
  input  ibex_pkg::wb_instr_type_e instr_type_wb_ex_i,
  input  logic [31:0]              pc_id_ex_i,
  input  logic                     instr_is_compressed_id_ex_i,
  input  logic                     instr_perf_count_id_ex_i,
  input  logic [4:0]               rf_waddr_id_ex_i,
  input  logic [31:0]              rf_wdata_id_ex_i,
  input  logic                     rf_we_id_ex_i,
  input  logic                     dummy_instr_id_ex_i,

  output  logic                     en_wb_ma_o,
  output  ibex_pkg::wb_instr_type_e instr_type_wb_ma_o,
  output  logic [31:0]              pc_id_ma_o,
  output  logic                     instr_is_compressed_id_ma_o,
  output  logic                     instr_perf_count_id_ma_o,
  output  logic [4:0]               rf_waddr_id_ma_o,
  output  logic [31:0]              rf_wdata_id_ma_o,
  output  logic                     rf_we_id_ma_o,
  output  logic                     dummy_instr_id_ma_o

);

  import ibex_pkg::*;

      // ALU
    ibex_pkg::alu_op_e     alu_operator_q;
    logic [31:0]           alu_operand_a_q;
    logic [31:0]           alu_operand_b_q;
    logic                  alu_instr_first_cycle_q;

  // Branch Target ALU
  // All of these signals are unusued when BranchTargetALU == 0
    logic [31:0]           bt_a_operand_q;
    logic [31:0]           bt_b_operand_q;

  // Multiplier/Divider
    ibex_pkg::md_op_e      multdiv_operator_q;
    logic                  mult_en_q;             // dynamic enable signal, for FSM control
    logic                  div_en_q;              // dynamic enable signal, for FSM control
    logic                  mult_sel_q;            // static decoder output, for data muxes
    logic                  div_sel_q;             // static decoder output, for data muxes
    logic  [1:0]           multdiv_signed_mode_q;
    logic [31:0]           multdiv_operand_a_q;
    logic [31:0]           multdiv_operand_b_q;
    logic                  multdiv_ready_id_q;
    logic                  data_ind_timing_q;

  // intermediate val reg
    logic [33:0]           imd_val_q_q[2];
  

  //to wb
    if (ResetAll) begin : id_ex_wb_n
      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            en_wb_ma_o <= '0;
            instr_type_wb_ma_o <= wb_instr_type_e'(0);
            pc_id_ma_o <= '0;
            instr_is_compressed_id_ma_o <= '0;
            instr_perf_count_id_ma_o <= '0;
            rf_waddr_id_ma_o <= '0;
            rf_wdata_id_ma_o <= '0;
            rf_we_id_ma_o <= '0;
            dummy_instr_id_ma_o <= '0;     
        end else begin
            en_wb_ma_o <= en_wb_ex_i;
            instr_type_wb_ma_o <= instr_type_wb_ex_i;
            pc_id_ma_o <= pc_id_ex_i;
            instr_is_compressed_id_ma_o <= instr_is_compressed_id_ex_i;
            instr_perf_count_id_ma_o <= instr_perf_count_id_ex_i;
            rf_waddr_id_ma_o <= rf_waddr_id_ex_i;
            rf_wdata_id_ma_o <= rf_wdata_id_ex_i;
            rf_we_id_ma_o <= rf_we_id_ex_i;
            dummy_instr_id_ma_o <= dummy_instr_id_ex_i;       
        end
      end
    end else begin : id_ex_wb
      always_ff @(posedge clk_i) begin
            en_wb_ma_o <= en_wb_ex_i;
            instr_type_wb_ma_o <= instr_type_wb_ex_i;
            pc_id_ma_o <= pc_id_ex_i;
            instr_is_compressed_id_ma_o <= instr_is_compressed_id_ex_i;
            instr_perf_count_id_ma_o <= instr_perf_count_id_ex_i;
            rf_waddr_id_ma_o <= rf_waddr_id_ex_i;
            rf_wdata_id_ma_o <= rf_wdata_id_ex_i;
            rf_we_id_ma_o <= rf_we_id_ex_i;
            dummy_instr_id_ma_o <= dummy_instr_id_ex_i;     
      end
    end


    //to lsu
    if (ResetAll) begin : id_ex_lsu_n
      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
          lsu_we_ma_o <= '0;             // write enable                     -> from ID/EX
          lsu_type_ma_o <= '0;           // data type: word, half word, byte -> from ID/EX
          lsu_wdata_ma_o <= '0;          // data to write to memory          -> from ID/EX
          lsu_sign_ext_ma_o <= '0;       // sign extension             
        end else begin
          lsu_we_ma_o <= lsu_we_ex_i;             // write enable                     -> from ID/EX
          lsu_type_ma_o <= lsu_type_ex_i;           // data type: word, half word, byte -> from ID/EX
          lsu_wdata_ma_o <= lsu_wdata_ex_i;          // data to write to memory          -> from ID/EX
          lsu_sign_ext_ma_o <= lsu_sign_ext_ex_i;       // sign extension   
        end
      end
    end else begin : id_ex_lsu
      always_ff @(posedge clk_i) begin
          lsu_we_ma_o <= lsu_we_ex_i;             // write enable                     -> from ID/EX
          lsu_type_ma_o <= lsu_type_ex_i;           // data type: word, half word, byte -> from ID/EX
          lsu_wdata_ma_o <= lsu_wdata_ex_i;          // data to write to memory          -> from ID/EX
          lsu_sign_ext_ma_o <= lsu_sign_ext_ex_i;       // sign extension   
      end
    end

    //id_ex pipeline
    if (ResetAll) begin : id_ex_n
      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
        // ALU
            alu_operator_q <= alu_op_e'(0);
            alu_operand_a_q <= '0;
            alu_operand_b_q <= '0;
            alu_instr_first_cycle_q <= '0;

        // Branch Target ALU
        // All of these signals are unusued when BranchTargetALU == 0
            bt_a_operand_q <= '0;
            bt_b_operand_q <= '0;

        // Multiplier/Divider
            multdiv_operator_q <= md_op_e'(0);
            mult_en_q <= '0;             // dynamic enable signal, for FSM control
            div_en_q <= '0;              // dynamic enable signal, for FSM control
            mult_sel_q <= '0;            // static decoder output, for data muxes
            div_sel_q <= '0;             // static decoder output, for data muxes
            multdiv_signed_mode_q <= '0;
            multdiv_operand_a_q <= '0;
            multdiv_operand_b_q <= '0;
            multdiv_ready_id_q <= '0;
            data_ind_timing_q <= '0;

        // intermediate val reg
            imd_val_q_q[0]  <= '0;
            imd_val_q_q[1]  <= '0;
        end else begin
        // ALU
            alu_operator_q <= alu_operator_i;
            alu_operand_a_q <= alu_operand_a_i;
            alu_operand_b_q <= alu_operand_b_i;
            alu_instr_first_cycle_q <= alu_instr_first_cycle_i;

        // Branch Target ALU
        // All of these signals are unusued when BranchTargetALU == 0
            bt_a_operand_q <= bt_a_operand_i;
            bt_b_operand_q <= bt_b_operand_i;

        // Multiplier/Divider
            multdiv_operator_q <= multdiv_operator_i;
            mult_en_q <= mult_en_i;             // dynamic enable signal, for FSM control
            div_en_q <= div_en_i;              // dynamic enable signal, for FSM control
            mult_sel_q <= mult_sel_i;            // static decoder output, for data muxes
            div_sel_q <= div_sel_i;             // static decoder output, for data muxes
            multdiv_signed_mode_q <= multdiv_signed_mode_i;
            multdiv_operand_a_q <= multdiv_operand_a_i;
            multdiv_operand_b_q <= multdiv_operand_b_i;
            multdiv_ready_id_q <= multdiv_ready_id_i;
            data_ind_timing_q <= data_ind_timing_i;

        // intermediate val reg
            imd_val_q_q[0]  <= imd_val_q_i[0];
            imd_val_q_q[1]  <= imd_val_q_i[1];
        end
      end
    end else begin : id_ex
      always_ff @(posedge clk_i) begin
                  // ALU
            alu_operator_q <= alu_operator_i;
            alu_operand_a_q <= alu_operand_a_i;
            alu_operand_b_q <= alu_operand_b_i;
            alu_instr_first_cycle_q <= alu_instr_first_cycle_i;

        // Branch Target ALU
        // All of these signals are unusued when BranchTargetALU == 0
            bt_a_operand_q <= bt_a_operand_i;
            bt_b_operand_q <= bt_b_operand_i;

        // Multiplier/Divider
            multdiv_operator_q <= multdiv_operator_i;
            mult_en_q <= mult_en_i;             // dynamic enable signal, for FSM control
            div_en_q <= div_en_i;              // dynamic enable signal, for FSM control
            mult_sel_q <= mult_sel_i;            // static decoder output, for data muxes
            div_sel_q <= div_sel_i;             // static decoder output, for data muxes
            multdiv_signed_mode_q <= multdiv_signed_mode_i;
            multdiv_operand_a_q <= multdiv_operand_a_i;
            multdiv_operand_b_q <= multdiv_operand_b_i;
            multdiv_ready_id_q <= multdiv_ready_id_i;
            data_ind_timing_q <= data_ind_timing_i;

        // intermediate val reg
            imd_val_q_q[0]  <= imd_val_q_i[0];
            imd_val_q_q[1]  <= imd_val_q_i[1];
      end
    end

  import ibex_pkg::*;

  logic [31:0] alu_result, multdiv_result;

  logic [32:0] multdiv_alu_operand_b, multdiv_alu_operand_a;
  logic [33:0] alu_adder_result_ext;
  logic        alu_cmp_result, alu_is_equal_result;
  logic        multdiv_valid;
  logic        multdiv_sel;
  logic [31:0] alu_imd_val_q[2];
  logic [31:0] alu_imd_val_d[2];
  logic [ 1:0] alu_imd_val_we;
  logic [33:0] multdiv_imd_val_d[2];
  logic [ 1:0] multdiv_imd_val_we;

  /*
    The multdiv_i output is never selected if RV32M=RV32MNone
    At synthesis time, all the combinational and sequential logic
    from the multdiv_i module are eliminated
  */
  if (RV32M != RV32MNone) begin : gen_multdiv_m
    assign multdiv_sel = mult_sel_q | div_sel_q;
  end else begin : gen_multdiv_no_m
    assign multdiv_sel = 1'b0;
  end

  // Intermediate Value Register Mux
  assign imd_val_d_o[0] = multdiv_sel ? multdiv_imd_val_d[0] : {2'b0, alu_imd_val_d[0]};
  assign imd_val_d_o[1] = multdiv_sel ? multdiv_imd_val_d[1] : {2'b0, alu_imd_val_d[1]};
  assign imd_val_we_o   = multdiv_sel ? multdiv_imd_val_we : alu_imd_val_we;

  assign alu_imd_val_q = '{imd_val_q_q[0][31:0], imd_val_q_q[1][31:0]};

  assign result_ex_o  = multdiv_sel ? multdiv_result : alu_result;

  // branch handling
  assign branch_decision_o  = alu_cmp_result;

  if (BranchTargetALU) begin : g_branch_target_alu
    logic [32:0] bt_alu_result;
    logic        unused_bt_carry;

    assign bt_alu_result   = bt_a_operand_q + bt_b_operand_q;

    assign unused_bt_carry = bt_alu_result[32];
    assign branch_target_o = bt_alu_result[31:0];
  end else begin : g_no_branch_target_alu
    // Unused bt_operand signals cause lint errors, this avoids them
    logic [31:0] unused_bt_a_operand, unused_bt_b_operand;

    assign unused_bt_a_operand = bt_a_operand_q;
    assign unused_bt_b_operand = bt_b_operand_q;

    assign branch_target_o = alu_adder_result_ex_o;
  end

  /////////
  // ALU //
  /////////

  ibex_alu #(
    .RV32B(RV32B)
  ) alu_i (
    .operator_i         (alu_operator_q),
    .operand_a_i        (alu_operand_a_q),
    .operand_b_i        (alu_operand_b_q),
    .instr_first_cycle_i(alu_instr_first_cycle_q),
    .imd_val_q_i        (alu_imd_val_q),
    .imd_val_we_o       (alu_imd_val_we),
    .imd_val_d_o        (alu_imd_val_d),
    .multdiv_operand_a_i(multdiv_alu_operand_a),
    .multdiv_operand_b_i(multdiv_alu_operand_b),
    .multdiv_sel_i      (multdiv_sel),
    .adder_result_o     (alu_adder_result_ex_o),
    .adder_result_ext_o (alu_adder_result_ext),
    .result_o           (alu_result),
    .comparison_result_o(alu_cmp_result),
    .is_equal_result_o  (alu_is_equal_result)
  );

  ////////////////
  // Multiplier //
  ////////////////

  if (RV32M == RV32MSlow) begin : gen_multdiv_slow
    ibex_multdiv_slow multdiv_i (
      .clk_i             (clk_i),
      .rst_ni            (rst_ni),
      .mult_en_i         (mult_en_q),
      .div_en_i          (div_en_q),
      .mult_sel_i        (mult_sel_q),
      .div_sel_i         (div_sel_q),
      .operator_i        (multdiv_operator_q),
      .signed_mode_i     (multdiv_signed_mode_q),
      .op_a_i            (multdiv_operand_a_q),
      .op_b_i            (multdiv_operand_b_q),
      .alu_adder_ext_i   (alu_adder_result_ext),
      .alu_adder_i       (alu_adder_result_ex_o),
      .equal_to_zero_i   (alu_is_equal_result),
      .data_ind_timing_i (data_ind_timing_q),
      .valid_o           (multdiv_valid),
      .alu_operand_a_o   (multdiv_alu_operand_a),
      .alu_operand_b_o   (multdiv_alu_operand_b),
      .imd_val_q_i       (imd_val_q_q),
      .imd_val_d_o       (multdiv_imd_val_d),
      .imd_val_we_o      (multdiv_imd_val_we),
      .multdiv_ready_id_i(multdiv_ready_id_q),
      .multdiv_result_o  (multdiv_result)
    );
  end else if (RV32M == RV32MFast || RV32M == RV32MSingleCycle) begin : gen_multdiv_fast
    ibex_multdiv_fast #(
      .RV32M(RV32M)
    ) multdiv_i (
      .clk_i             (clk_i),
      .rst_ni            (rst_ni),
      .mult_en_i         (mult_en_q),
      .div_en_i          (div_en_q),
      .mult_sel_i        (mult_sel_q),
      .div_sel_i         (div_sel_q),
      .operator_i        (multdiv_operator_q),
      .signed_mode_i     (multdiv_signed_mode_q),
      .op_a_i            (multdiv_operand_a_q),
      .op_b_i            (multdiv_operand_b_q),
      .alu_operand_a_o   (multdiv_alu_operand_a),
      .alu_operand_b_o   (multdiv_alu_operand_b),
      .alu_adder_ext_i   (alu_adder_result_ext),
      .alu_adder_i       (alu_adder_result_ex_o),
      .equal_to_zero_i   (alu_is_equal_result),
      .data_ind_timing_i (data_ind_timing_q),
      .imd_val_q_i       (imd_val_q_q),
      .imd_val_d_o       (multdiv_imd_val_d),
      .imd_val_we_o      (multdiv_imd_val_we),
      .multdiv_ready_id_i(multdiv_ready_id_q),
      .valid_o           (multdiv_valid),
      .multdiv_result_o  (multdiv_result)
    );
  end

  // Multiplier/divider may require multiple cycles. The ALU output is valid in the same cycle
  // unless the intermediate result register is being written (which indicates this isn't the
  // final cycle of ALU operation).
  assign ex_valid_o = multdiv_sel ? multdiv_valid : ~(|alu_imd_val_we);

endmodule
