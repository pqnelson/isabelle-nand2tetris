\<^marker>\<open>creator "Alex Nelson"\<close>
chapter \<open>Combinational Logic Gates and the ALU\<close>
theory CombinationalCircuits
  imports Main "~~/src/HOL/Library/Z2" HOL.Sledgehammer
begin

section \<open>Introduction\<close>

text \<open>This begins with the definition of the NAND logic gate, then builds the other logic gates out
of it. We then introduce the Hexadecimal counterpart gates, and finally the 16-bit word gates.
This culminates in the implementation of the Arithmetic Logical Unit (ALU) for the Hack 
architecture.\<close>

section \<open>Basic Logic Gates\<close>

fun NAND :: \<open>bit \<Rightarrow> bit \<Rightarrow> bit\<close> where
\<open>NAND (1::bit) (1::bit) = (0::bit)\<close> |
\<open>NAND (1::bit) (0::bit) = (1::bit)\<close> |
\<open>NAND (0::bit) (1::bit) = (1::bit)\<close> |
\<open>NAND (0::bit) (0::bit) = (1::bit)\<close>

lemma NAND_a_0 [simp]: "NAND a 0 = 1"
  by (case_tac a) auto

lemma NAND_0_b [simp]: "NAND 0 b = 1"
  by (case_tac b) auto

theorem NAND_comm: "NAND a b = NAND b a"
  by (case_tac b; case_tac a) auto

definition NOT :: \<open>bit \<Rightarrow> bit\<close>
  where [simp]: \<open>NOT a \<equiv> (NAND a a)\<close>

lemma NOT_0 [simp]: "NOT (0::bit) = (1::bit)"
  by simp

lemma NOT_1 [simp]: "NOT (1::bit) = (0::bit)"
  by simp

theorem NOT_NOT: "NOT (NOT a) = a"
  by (case_tac a) auto

definition AND :: \<open>bit \<Rightarrow> bit \<Rightarrow> bit\<close>
  where [simp]: \<open>AND a b \<equiv> NAND (NAND a b) (NAND a b)\<close>

lemma AND_0_0: "AND (0::bit) (0::bit) = (0::bit)"
  by simp

lemma AND_0_1: "AND (0::bit) (1::bit) = (0::bit)"
  by simp

lemma AND_1_0: "AND (1::bit) (0::bit) = (0::bit)"
  by simp

lemma AND_1_1: "AND (1::bit) (1::bit) = (1::bit)"
  by simp

lemma AND_a_1 [simp]: "AND a 1 = a"
  by (case_tac a) auto

lemma AND_a_0 [simp]: "AND a 0 = 0"
  by (case_tac a) auto

lemma AND_1_b [simp]: "AND 1 b = b"
  by (case_tac b) auto

lemma AND_0_b [simp]: "AND 0 b = 0"
  by (case_tac b) auto

theorem AND_comm: "AND a b = AND b a"
  using AND_0_b AND_a_0 AND_1_b AND_a_1 by (case_tac b) auto

\<comment>\<open>We can prove that NAND really is just "NOT AND"!\<close>
lemma NOT_AND_is_NAND: "NOT (AND a b) = NAND a b"
  by (case_tac b; case_tac a) auto

definition OR :: \<open>bit \<Rightarrow> bit \<Rightarrow> bit\<close>
  where [simp]: \<open>OR a b \<equiv> NAND (NOT a) (NOT b)\<close>

lemma OR_0_0: "OR (0::bit) (0::bit) = (0::bit)"
  by simp

lemma OR_0_1: "OR (0::bit) (1::bit) = (1::bit)"
  by simp

lemma OR_1_0: "OR (1::bit) (0::bit) = (1::bit)"
  by simp

lemma OR_1_1: "OR (1::bit) (1::bit) = (1::bit)"
  by simp

lemma OR_a_0 [simp]: "OR a 0 = a"
  by (case_tac a) auto

lemma OR_0_b [simp]: "OR 0 b = b"
  by (case_tac b) auto

lemma OR_a_1: "OR a 1 = 1"
  by simp

lemma OR_1_b: "OR 1 b = 1"
  by simp

theorem OR_comm: "OR a b = OR b a"
  by (simp add: NAND_comm)

lemma NOT_AND_NOT: "NOT (AND (NOT a) (NOT b)) = OR a b"
  using NOT_NOT by auto

theorem de_Morgan_gate1: "NOT (AND a b) = OR (NOT a) (NOT b)"
  using NOT_NOT by force

theorem de_Morgan_gate2: "NOT (OR a b) = AND (NOT a) (NOT b)"
  by (case_tac a) auto

(* Only 4 logic gates are needed. *)
definition XOR :: \<open>bit \<Rightarrow> bit \<Rightarrow> bit\<close>
  where [simp]: \<open>XOR a b \<equiv> NAND (NAND a (NAND a b)) (NAND b (NAND a b))\<close>

lemma XOR_0_0: "XOR 0 0 = 0"
  by simp

lemma XOR_0_1: "XOR 0 1 = 1"
  by simp

lemma XOR_1_0: "XOR 1 0 = 1"
  by simp

lemma XOR_1_1: "XOR 1 1 = 0"
  by simp

definition MUX :: \<open>bit \<Rightarrow> bit \<Rightarrow> bit \<Rightarrow> bit\<close>
  where \<open>MUX a b s \<equiv> NAND (NAND a (NOT s)) (NAND b s)\<close>

(* MUX_left and right suffice for specifying its behaviour. *)
theorem MUX_left [simp]: "MUX a b 0 = a"
  using MUX_def by (case_tac a) auto

theorem MUX_right [simp]: "MUX a b 1 = b"
  using MUX_def by (case_tac b) auto

lemma MUX_alt: "MUX a b s = OR (AND a (NOT s)) (AND b s)"
  using MUX_def NOT_AND_is_NAND by auto

(* The implementation of DMUX is not as important as its defining properties,
which we prove immediately and add to the simplification tactic. *)
definition DMUX :: \<open>bit \<Rightarrow> bit \<Rightarrow> (bit * bit)\<close>
  where \<open>DMUX i s \<equiv> (AND i (NOT s), AND i s)\<close>

lemma DMUX_left [simp]: "DMUX i 0 = (i, 0)"
  using AND_a_1 DMUX_def by auto

lemma DMUX_right [simp]: "DMUX i 1 = (0, i)"
  using AND_a_1 DMUX_def by auto

(* Only 9 NAND gates are needed for the FULLADDER, returns (sum, carry). *)
definition FULLADDER :: \<open>bit \<Rightarrow> bit \<Rightarrow> bit \<Rightarrow> (bit * bit)\<close> where
  "FULLADDER a b c \<equiv> let nab = NAND a b 
  in let sab = NAND (NAND b nab) (NAND a nab)
  in let scab = NAND sab c
  in (NAND (NAND scab sab) (NAND scab c), NAND nab scab)"

lemma FULLADDER_000 [simp]: "FULLADDER 0 0 0 = (0, 0)"
  by (simp add: FULLADDER_def)

lemma FULLADDER_001 [simp]: "FULLADDER 0 0 1 = (1, 0)"
  by (simp add: FULLADDER_def)

lemma FULLADDER_010 [simp]: "FULLADDER 0 1 0 = (1, 0)"
  by (simp add: FULLADDER_def)

lemma FULLADDER_011 [simp]: "FULLADDER 0 1 1 = (0, 1)"
  by (simp add: FULLADDER_def)

lemma FULLADDER_100 [simp]: "FULLADDER 1 0 0 = (1, 0)"
  by (simp add: FULLADDER_def)

lemma FULLADDER_101 [simp]: "FULLADDER 1 0 1 = (0, 1)"
  by (simp add: FULLADDER_def)

lemma FULLADDER_110 [simp]: "FULLADDER 1 1 0 = (0, 1)"
  by (simp add: FULLADDER_def)

lemma FULLADDER_111 [simp]: "FULLADDER 1 1 1 = (1, 1)"
  by (simp add: FULLADDER_def)

lemma FULLADDER_00c: "FULLADDER 0 0 c = (c,0)"
  by (metis (full_types) FULLADDER_000 FULLADDER_001 bit.exhaust) 

lemma FULLADDER_0bc: "FULLADDER 0 b c = (XOR b c,AND b c)"
proof - (* 46 ms *)
  have "\<forall>b. AND 1 b = b"
    using AND_1_b by blast
  moreover have "(FULLADDER 0 b c = (XOR b 1, 0) \<and> b \<noteq> 1) \<and> c \<noteq> 0 \<or> FULLADDER 0 b c = (XOR b c, 0) \<and> b \<noteq> 1 \<or> FULLADDER 0 b c = (XOR b c, c) \<and> b \<noteq> 0 \<or> FULLADDER 0 b c = (XOR 1 c, AND b c) \<and> b \<noteq> 0"
    by (smt (z3) FULLADDER_00c FULLADDER_010 FULLADDER_011 XOR_0_0 XOR_0_1 XOR_1_0 XOR_1_1 bit_not_zero_iff)
  ultimately show ?thesis
    by fastforce
qed

lemma FULLADDER_a0c: "FULLADDER a 0 c = (XOR a c,AND a c)"
proof - (* 18 ms *)
  have f1: "FULLADDER 1 0 0 = (1, 0)"
    using FULLADDER_100 by blast
  have "FULLADDER 0 1 0 = (1, 0)"
    using FULLADDER_010 by blast
  then show ?thesis
    using f1 by (smt (z3) FULLADDER_011 FULLADDER_0bc FULLADDER_101 bit_not_zero_iff)
qed

lemma FULLADDER_a00: "FULLADDER a 0 0 = (a,0)"
  by (case_tac a) auto

lemma FULLADDER_0b0: "FULLADDER 0 b 0 = (b,0)"
  by (case_tac b) auto

lemma FULLADDER_abc: "FULLADDER a b c = (XOR a (XOR b c),OR (AND a b) (AND c (XOR a b)))"
proof - (* 72ms *)
  { assume "0 \<noteq> b"
    moreover
    { assume "0 \<noteq> b \<and> 0 \<noteq> a"
      then have "0 \<noteq> c \<and> 0 \<noteq> b \<and> 0 \<noteq> a \<or> FULLADDER 1 1 c = (XOR 1 (XOR 1 c), 1) \<and> 0 \<noteq> a \<and> 0 \<noteq> b"
        using FULLADDER_110 XOR_1_0 XOR_1_1 by presburger
      then have ?thesis
        by fastforce }
    ultimately have "1 = a \<longrightarrow> FULLADDER a b c = (XOR a (XOR b c), OR (AND a b) (AND c (XOR a b)))"
      by blast }
  moreover
  { assume "1 \<noteq> a"
    then have "1 \<noteq> a \<and> 1 \<noteq> b \<or> (XOR 0 (XOR b 0), 0::bit) = (b, 0) \<and> 1 \<noteq> c \<and> 1 \<noteq> a \<or> FULLADDER 0 b c = (XOR 0 (XOR b c), AND c (XOR 0 b)) \<and> 1 \<noteq> a"
      using AND_1_b FULLADDER_011 XOR_0_0 XOR_0_1 XOR_1_0 XOR_1_1 by presburger
    then have "(XOR 0 (XOR b 0), 0::bit) = (b, 0) \<and> 1 \<noteq> c \<and> 1 \<noteq> a \<or> FULLADDER 0 b c = (XOR 0 (XOR b c), AND c (XOR 0 b)) \<and> 1 \<noteq> a"
      by fastforce
    then have ?thesis
      using FULLADDER_0b0 OR_0_b by fastforce }
  ultimately show ?thesis
    by (smt (z3) AND_0_b AND_1_b FULLADDER_101 FULLADDER_a00 OR_0_b XOR_0_0 XOR_0_1 XOR_1_0 XOR_1_1 bit_not_zero_iff)
qed

lemma FULLADDER_carry_criteria: "(s,1) = FULLADDER a b c \<longrightarrow> (a = 1 \<and> b = 1) \<or> (c = 1 \<and> a = 1 \<and> b = 0) \<or> (c = 1 \<and> a = 0 \<and> b = 1)"
proof - (* 55ms, fastest proof I could find *)
  have A1: "1 = c \<or> c = 0"
    by force
  have A2: "1 = b \<or> b = 0"
    by force
  have "1 = a \<or> a = 0"
    by force
  moreover
  { assume "b \<noteq> 0"
    then have "1 = a \<longrightarrow> (s, 1) \<noteq> FULLADDER a b c \<or> 1 = a \<and> 1 = b \<or> 1 = c \<and> 1 = a \<and> b = 0 \<or> 1 = c \<and> a = 0 \<and> 1 = b"
      by simp }
  ultimately show ?thesis
    using A2 A1 by (smt (z3) FULLADDER_000 FULLADDER_001 FULLADDER_010 FULLADDER_100 Pair_inject)
qed

theorem FULLADDER_comm: "FULLADDER a b c = FULLADDER b a c"
proof - (* 82 ms *)
  have "\<forall>b. (b::bit) = 1 \<or> b = 0"
    using bit_not_zero_iff by blast
  then show ?thesis
    by (smt (z3) FULLADDER_0bc FULLADDER_a0c)
qed

definition MUX4WAY :: \<open>bit \<Rightarrow> bit \<Rightarrow> bit \<Rightarrow> bit \<Rightarrow> bit \<Rightarrow> bit \<Rightarrow> bit\<close>
  where \<open>MUX4WAY a b c d s0 s1 \<equiv> MUX (MUX a b s1) (MUX c d s1) s0\<close>

lemma MUX4WAY_00 [simp]: "MUX4WAY a b c d 0 0 = a" by (simp add: MUX4WAY_def)
lemma MUX4WAY_01 [simp]: "MUX4WAY a b c d 0 1 = b" by (simp add: MUX4WAY_def)
lemma MUX4WAY_10 [simp]: "MUX4WAY a b c d 1 0 = c" by (simp add: MUX4WAY_def)
lemma MUX4WAY_11 [simp]: "MUX4WAY a b c d 1 1 = d" by (simp add: MUX4WAY_def)

definition MUX8WAY :: \<open>bit \<Rightarrow> bit \<Rightarrow> bit \<Rightarrow> bit \<Rightarrow> bit \<Rightarrow> bit \<Rightarrow> bit \<Rightarrow> bit \<Rightarrow> bit \<Rightarrow> bit \<Rightarrow> bit \<Rightarrow> bit\<close>
  where \<open>MUX8WAY a b c d e f g h s0 s1 s2 \<equiv> MUX (MUX4WAY a b c d s1 s2) (MUX4WAY e f g h s1 s2) s0\<close>

lemma MUX8WAY_000 [simp]: "MUX8WAY a b c d e f g h 0 0 0 = a" by (simp add: MUX8WAY_def)
lemma MUX8WAY_001 [simp]: "MUX8WAY a b c d e f g h 0 0 1 = b" by (simp add: MUX8WAY_def)
lemma MUX8WAY_010 [simp]: "MUX8WAY a b c d e f g h 0 1 0 = c" by (simp add: MUX8WAY_def)
lemma MUX8WAY_011 [simp]: "MUX8WAY a b c d e f g h 0 1 1 = d" by (simp add: MUX8WAY_def)
lemma MUX8WAY_100 [simp]: "MUX8WAY a b c d e f g h 1 0 0 = e" by (simp add: MUX8WAY_def)
lemma MUX8WAY_101 [simp]: "MUX8WAY a b c d e f g h 1 0 1 = f" by (simp add: MUX8WAY_def)
lemma MUX8WAY_110 [simp]: "MUX8WAY a b c d e f g h 1 1 0 = g" by (simp add: MUX8WAY_def)
lemma MUX8WAY_111 [simp]: "MUX8WAY a b c d e f g h 1 1 1 = h" by (simp add: MUX8WAY_def)

section \<open>Hexadecimal and Machine words\<close>
text \<open> Since the book associated with Nand2Tetris uses Big Endian convention, I follow their
  convention. Realistically, we should refactor this out, so as to force the user to import
  their desired Endianess.

  I have also decided to include "helper abbreviations" to refer to Hex instances by, well,
  their hexadecimal values X3, X4, ..., XF. I'm sure there is a way to hack the Isabelle 
  parser to automatically transform 0x1, 0x2, ..., 0xF into Hex instances, but that seems
  too crazy for me at the moment. \<close>

datatype Hex = Hex bit bit bit bit

instantiation Hex :: zero_neq_one
begin

definition zero_Hex :: Hex
  where \<open>0 = Hex 0 0 0 0\<close>

definition one_Hex :: Hex
  where \<open>1 = Hex 0 0 0 1\<close>

instance
  by standard (simp add: one_Hex_def zero_Hex_def)
end

abbreviation Two_Hex :: Hex ("X2")
  where \<open>X2 \<equiv> Hex 0 0 1 0\<close>

abbreviation Three_Hex :: Hex ("X3")
  where \<open>X3 \<equiv> Hex 0 0 1 1\<close>

abbreviation Four_Hex :: Hex ("X4")
  where \<open>X4 \<equiv> Hex 0 1 0 0\<close>

abbreviation Five_Hex :: Hex ("X5")
  where \<open>X5 \<equiv> Hex 0 1 0 1\<close>

abbreviation Six_Hex :: Hex ("X6")
  where \<open>X6 \<equiv> Hex 0 1 1 0\<close>

abbreviation Seven_Hex :: Hex ("X7")
  where \<open>X7 \<equiv> Hex 0 1 1 1\<close>

abbreviation Eight_Hex :: Hex ("X8")
  where \<open>X8 \<equiv> Hex 1 0 0 0\<close>

abbreviation Nine_Hex :: Hex ("X9")
  where \<open>X9 \<equiv> Hex 1 0 0 1\<close>

abbreviation A_Hex :: Hex ("XA")
  where \<open>XA \<equiv> Hex 1 0 1 0\<close>

abbreviation B_Hex :: Hex ("XB")
  where \<open>XB \<equiv> Hex 1 0 1 1\<close>

abbreviation C_Hex :: Hex ("XC")
  where \<open>XC \<equiv> Hex 1 1 0 0\<close>

abbreviation D_Hex :: Hex ("XD")
  where \<open>XD \<equiv> Hex 1 1 0 1\<close>

abbreviation E_Hex :: Hex ("XE")
  where \<open>XE \<equiv> Hex 1 1 1 0\<close>

abbreviation F_Hex :: Hex ("XF")
  where \<open>XF \<equiv> Hex 1 1 1 1\<close>

\<comment>\<open>A smoke check on the abbreviations\<close>
lemma "XF = Hex 1 1 1 1" by auto

datatype Word = Word Hex Hex Hex Hex

fun bit_to_nat :: "bit \<Rightarrow> nat" where
  "bit_to_nat 0 = 0"
| "bit_to_nat 1 = 1"

lemma bit_unsigned_max: "bit_to_nat b < 2"
  by (case_tac b) auto

lemma bit_to_nat_ubound: "bit_to_nat b \<le> 1"
  by (case_tac b) auto

fun Hex_to_nat :: "Hex \<Rightarrow> nat" where
  "Hex_to_nat (Hex a b c d) = (bit_to_nat d) + 2*(bit_to_nat c)
                              + 4*(bit_to_nat b) + 8*(bit_to_nat a)"

fun Word_to_nat :: "Word \<Rightarrow> nat" where
  "Word_to_nat (Word h1 h2 h3 h4) = (Hex_to_nat h4) + 16*(Hex_to_nat h3) + 256*(Hex_to_nat h2)
                                    + 4096*(Hex_to_nat h1)"

definition nat_to_Hex :: "nat \<Rightarrow> Hex" where
[simp]: "nat_to_Hex n \<equiv> (case (n mod 16) of
 0 \<Rightarrow> (Hex 0 0 0 0)
 | (Suc 0) \<Rightarrow> (Hex 0 0 0 1)
 | (Suc (Suc 0)) \<Rightarrow> (Hex 0 0 1 0)
 | (Suc (Suc (Suc 0))) \<Rightarrow> (Hex 0 0 1 1)
 | (Suc (Suc (Suc (Suc 0)))) \<Rightarrow> (Hex 0 1 0 0)
 | (Suc (Suc (Suc (Suc (Suc 0))))) \<Rightarrow> (Hex 0 1 0 1)
 | (Suc (Suc (Suc (Suc (Suc (Suc 0)))))) \<Rightarrow> (Hex 0 1 1 0)
 | (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))) \<Rightarrow> (Hex 0 1 1 1)
 | (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))) \<Rightarrow> (Hex 1 0 0 0)
 | (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))))) \<Rightarrow> (Hex 1 0 0 1)
 | (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))) \<Rightarrow> (Hex 1 0 1 0)
 | (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))))))) \<Rightarrow> (Hex 1 0 1 1)
 | (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))) \<Rightarrow> (Hex 1 1 0 0)
 | (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))))))))) \<Rightarrow> (Hex 1 1 0 1)
 | (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))))))))) \<Rightarrow> (Hex 1 1 1 0)
 |_ \<Rightarrow> (Hex 1 1 1 1))"

(* Some smoke checks to make sure the conversions work as expected. *)
lemma "nat_to_Hex 0x0 = Hex 0 0 0 0" by simp
lemma "nat_to_Hex 0x1 = Hex 0 0 0 1" by simp
lemma "nat_to_Hex 0x2 = Hex 0 0 1 0" by simp
lemma "nat_to_Hex 0x3 = Hex 0 0 1 1" by simp
lemma "nat_to_Hex 0x4 = Hex 0 1 0 0" by simp
lemma "nat_to_Hex 0x5 = Hex 0 1 0 1" by simp
lemma "nat_to_Hex 0x6 = Hex 0 1 1 0" by simp
lemma "nat_to_Hex 0x7 = Hex 0 1 1 1" by simp
lemma "nat_to_Hex 0x8 = Hex 1 0 0 0" by simp
lemma "nat_to_Hex 0x9 = Hex 1 0 0 1" by simp
lemma "nat_to_Hex 0xA = Hex 1 0 1 0" by simp
lemma "nat_to_Hex 0xB = Hex 1 0 1 1" by simp
lemma "nat_to_Hex 0xC = Hex 1 1 0 0" by simp
lemma "nat_to_Hex 0xD = Hex 1 1 0 1" by simp
lemma "nat_to_Hex 0xE = Hex 1 1 1 0" by simp
lemma "nat_to_Hex 0xF = Hex 1 1 1 1" by simp

lemma Hex_unsigned_max: "Hex_to_nat x < 16"
proof (cases x)
  case A1: (Hex x1 x2 x3 x4)
  moreover have "Hex_to_nat x = (bit_to_nat x4) + 2*(bit_to_nat x3) + 4*(bit_to_nat x2) + 8*(bit_to_nat x1)"
    using A1 by simp
  ultimately have "Hex_to_nat x \<le> 1 + 2*1 + 4*1 + 8*1"
    by (metis add_mono_thms_linordered_semiring(1) bit_to_nat_ubound mult_le_mono2)
  thus ?thesis by simp
qed

lemma Hex_to_nat_mod16 [simp]: "(Hex_to_nat x) mod 16 = Hex_to_nat x"
  by (simp add: Hex_unsigned_max)

(* I hate tactical proofs, but if I wrote this out in structured Isar, it'd be ridiculously long
and boil down to "by simp" repeated over and over. *)
theorem Hex_to_nat_to_Hex: "nat_to_Hex (Hex_to_nat a) = a"
  by (case_tac a; case_tac x1; case_tac x2; case_tac x3; case_tac x4) simp+

fun nat_to_Word :: "nat \<Rightarrow> Word" where
"nat_to_Word n = Word (nat_to_Hex ((n div 4096) mod 16)) (nat_to_Hex ((n div 256) mod 16))
  (nat_to_Hex ((n div 16) mod 16)) (nat_to_Hex (n mod 16))"

theorem Word_to_nat_to_Word: "nat_to_Word (Word_to_nat a) = a"
proof (cases a)
  case A: (Word a1 a2 a3 a4)
  have A1: "(((Hex_to_nat a4) + 16*(Hex_to_nat a3) + 256*(Hex_to_nat a2) + 4096*(Hex_to_nat a1)) div 4096) mod 16 = (Hex_to_nat a1)"
  proof-
    have "(Hex_to_nat a4) < 16 \<and> (Hex_to_nat a3) < 16 \<and> Hex_to_nat a2 < 16" 
      using Hex_unsigned_max by auto
    then have "(Hex_to_nat a4) + 16*(Hex_to_nat a3) + 256*(Hex_to_nat a2) \<le> 15 + 16*15 + 256*15"
      by linarith
    then have "(Hex_to_nat a4) + 16*(Hex_to_nat a3) + 256*(Hex_to_nat a2) < 4096" by simp
    then show ?thesis
      by simp
  qed
  then have N1: "nat_to_Hex((((Hex_to_nat a4) + 16*(Hex_to_nat a3) + 256*(Hex_to_nat a2) + 4096*(Hex_to_nat a1)) div 4096) mod 16) = a1" using Hex_to_nat_to_Hex by auto
  have "((Hex_to_nat a4) + 16*(Hex_to_nat a3) + 256*(Hex_to_nat a2) + 4096*(Hex_to_nat a1)) div 256 = (Hex_to_nat a2) + 16*(Hex_to_nat a1)"
  proof-
    have "(Hex_to_nat a4) < 16 \<and> (Hex_to_nat a3) < 16" using Hex_unsigned_max by auto
    then have "(Hex_to_nat a4) + 16*(Hex_to_nat a3) \<le> 15 + 16*15" by linarith
    then have "(Hex_to_nat a4) + 16*(Hex_to_nat a3) \<le> 255" by auto
    moreover have "((Hex_to_nat a4) + 16*(Hex_to_nat a3) + 256*(Hex_to_nat a2) + 4096*(Hex_to_nat a1)) =
     (((Hex_to_nat a4) + 16*(Hex_to_nat a3)) + 256*((Hex_to_nat a2) + 16*(Hex_to_nat a1)))"
    by simp
    ultimately show ?thesis
      using Euclidean_Rings.div_eq_0_iff div_mult_self2 eval_nat_numeral(2) less_Suc_eq_le by linarith
  qed
  then have A2: "(((Hex_to_nat a4) + 16*(Hex_to_nat a3) + 256*(Hex_to_nat a2) + 4096*(Hex_to_nat a1)) div 256) mod 16 = (Hex_to_nat a2)"
    using Hex_to_nat_mod16 by presburger
  then have N2: "nat_to_Hex((((Hex_to_nat a4) + 16*(Hex_to_nat a3) + 256*(Hex_to_nat a2) + 4096*(Hex_to_nat a1)) div 256) mod 16) = a2" using Hex_to_nat_to_Hex by auto

  have A3: "(((Hex_to_nat a4) + 16*(Hex_to_nat a3) + 256*(Hex_to_nat a2) + 4096*(Hex_to_nat a1)) div 16) mod 16 = Hex_to_nat a3"
  proof-
    have "(Hex_to_nat a4) + 16*(Hex_to_nat a3) + 256*(Hex_to_nat a2) + 4096*(Hex_to_nat a1)
        = (Hex_to_nat a4) + 16*(Hex_to_nat a3) + (16*16)*(Hex_to_nat a2) + (16*256)*(Hex_to_nat a1)" by auto
    then have "(Hex_to_nat a4) + 16*(Hex_to_nat a3) + 256*(Hex_to_nat a2) + 4096*(Hex_to_nat a1)
        = (Hex_to_nat a4) + 16*((Hex_to_nat a3) + 16*(Hex_to_nat a2) + 256*(Hex_to_nat a1))" by auto
    then have "((Hex_to_nat a4) + 16*(Hex_to_nat a3) + 256*(Hex_to_nat a2) + 4096*(Hex_to_nat a1)) = (((Hex_to_nat a4) + 16*((Hex_to_nat a3) + 16*((Hex_to_nat a2) + 16*(Hex_to_nat a1)))))"
      by auto
    moreover have "((Hex_to_nat a4) + 16*((Hex_to_nat a3) + 16*((Hex_to_nat a2) + 16*(Hex_to_nat a1)))) div 16 = ((Hex_to_nat a3) + 16*((Hex_to_nat a2) + 16*(Hex_to_nat a1)))"
      by (metis Hex_to_nat_mod16 div_mult_self2 mod_eq_self_iff_div_eq_0 nat_arith.rule0 zero_neq_numeral)
    moreover have "((Hex_to_nat a3) + 16*((Hex_to_nat a2) + 16*(Hex_to_nat a1))) mod 16 = (Hex_to_nat a3)"
      using Hex_to_nat_mod16 by presburger
    ultimately show ?thesis 
      by presburger
  qed
  then have "(((Hex_to_nat a4) + 16*(Hex_to_nat a3) + 256*(Hex_to_nat a2) + 4096*(Hex_to_nat a1)) div 16) mod 16 = Hex_to_nat a3"
    by auto
  then have N3: "nat_to_Hex((((Hex_to_nat a4) + 16*(Hex_to_nat a3) + 256*(Hex_to_nat a2) + 4096*(Hex_to_nat a1)) div 16) mod 16) = a3"
    using Hex_to_nat_to_Hex by presburger
  have "((Hex_to_nat a4) + 16*((Hex_to_nat a3) + 16*(Hex_to_nat a2) + 256*(Hex_to_nat a1))) mod 16 = Hex_to_nat a4"
    using Hex_to_nat_mod16 by presburger
  then have A4: "(Hex_to_nat a4 + 16 * Hex_to_nat a3 + 256 * Hex_to_nat a2 + 4096 * Hex_to_nat a1) mod 16 = Hex_to_nat a4"
    by (smt (verit, del_insts) \<open>(Hex_to_nat a4 + 16 * (Hex_to_nat a3 + 16 * Hex_to_nat a2 + 256 * Hex_to_nat a1)) mod 16 = Hex_to_nat a4\<close> ab_semigroup_add_class.add_ac(1) distrib_left_numeral mult_numeral_left_semiring_numeral semiring_norm(12) semiring_norm(13))
  then have N4: "a4 = nat_to_Hex (((Hex_to_nat a4) + 16*(Hex_to_nat a3) + 256*(Hex_to_nat a2)
     + 4096*(Hex_to_nat a1)) mod 16)"
    using Hex_to_nat_to_Hex by presburger
  have "nat_to_Word ((Hex_to_nat a4) + 16*(Hex_to_nat a3) + 256*(Hex_to_nat a2) + 4096*(Hex_to_nat a1)) 
    = Word (nat_to_Hex ((((Hex_to_nat a4) + 16*(Hex_to_nat a3) + 256*(Hex_to_nat a2) + 4096*(Hex_to_nat a1)) div 4096) mod 16))
           (nat_to_Hex ((((Hex_to_nat a4) + 16*(Hex_to_nat a3) + 256*(Hex_to_nat a2) + 4096*(Hex_to_nat a1)) div 256) mod 16))
           (nat_to_Hex ((((Hex_to_nat a4) + 16*(Hex_to_nat a3) + 256*(Hex_to_nat a2) + 4096*(Hex_to_nat a1)) div 16) mod 16))
           (nat_to_Hex (((Hex_to_nat a4) + 16*(Hex_to_nat a3) + 256*(Hex_to_nat a2) + 4096*(Hex_to_nat a1)) mod 16))"
    using A N1 N2 N3 N4 Hex_to_nat_to_Hex by auto
  then have "Word a1 a2 a3 a4 = 
    nat_to_Word ((Hex_to_nat a4) + 16*(Hex_to_nat a3) + 256*(Hex_to_nat a2) + 4096*(Hex_to_nat a1))"
    using A N1 N2 N3 N4 Hex_to_nat_to_Hex by auto
  then have "a = nat_to_Word ((Hex_to_nat a4) + 16*(Hex_to_nat a3) + 256*(Hex_to_nat a2)
                 + 4096*(Hex_to_nat a1))"
    using A by auto
  then show ?thesis
    using A Word_to_nat.simps by presburger
qed

lemma Word_unsigned_max: "Word_to_nat w < 65536"
proof (cases w)
  case A1: (Word w1 w2 w3 w4)
  then have A2: "Hex_to_nat w1 \<le> 15 \<and> Hex_to_nat w2 \<le> 15 \<and> Hex_to_nat w3 \<le> 15 \<and> Hex_to_nat w4 \<le> 15"
    using Hex_unsigned_max
    by (metis eval_nat_numeral(2) less_Suc_eq_le semiring_norm(26) semiring_norm(27))
  moreover have "Word_to_nat w = (Hex_to_nat w4) + 16*(Hex_to_nat w3) + 256*(Hex_to_nat w2)
                                 + 4096*(Hex_to_nat w1)"
    by (simp add: A1)
  ultimately have A3: "Word_to_nat w < 16 + 16*15 + 256*15 + 4096*15"
    by auto
  then show ?thesis by simp
qed

lemma Word_to_nat_mod65536: "(Word_to_nat w) mod 65536 = Word_to_nat w"
  by (simp add: Word_unsigned_max)

fun sign_bit :: \<open>Word \<Rightarrow> bit\<close> where
  "sign_bit (Word (Hex s _ _ _) _ _ _) = s"

section \<open>Logic Gates for Hexadecimals\<close>

fun NOT_Hex :: \<open>Hex \<Rightarrow> Hex\<close>
  where \<open>NOT_Hex (Hex a b c d) = Hex (NOT a) (NOT b) (NOT c) (NOT d)\<close>

lemma NOT_NOT_Hex: "NOT_Hex (NOT_Hex a) = a"
  using NOT_NOT by (case_tac a) auto

fun AND_Hex :: \<open>Hex \<Rightarrow> Hex \<Rightarrow> Hex\<close> where
  "AND_Hex (Hex a1 b1 c1 d1) (Hex a2 b2 c2 d2) = Hex (AND a1 a2) (AND b1 b2) (AND c1 c2) (AND d1 d2)"

lemma AND_Hex_x_F: "AND_Hex x XF = x"
  using AND_a_1 by (case_tac x) simp

lemma AND_Hex_F_x: "AND_Hex XF x = x"
  using AND_1_b by (case_tac x) simp

fun OR_Hex :: \<open>Hex \<Rightarrow> Hex \<Rightarrow> Hex\<close> where
  "OR_Hex (Hex a1 b1 c1 d1) (Hex a2 b2 c2 d2) = Hex (OR a1 a2) (OR b1 b2) (OR c1 c2) (OR d1 d2)"

lemma NOT_AND_NOT_Hex: "NOT_Hex (AND_Hex (NOT_Hex a) (NOT_Hex b)) = OR_Hex a b"
  using NOT_AND_NOT NOT_AND_is_NAND by (case_tac a; case_tac b) fastforce

fun XOR_Hex :: \<open>Hex \<Rightarrow> Hex \<Rightarrow> Hex\<close> where
  "XOR_Hex (Hex a1 b1 c1 d1) (Hex a2 b2 c2 d2) = Hex (XOR a1 a2) (XOR b1 b2) (XOR c1 c2) (XOR d1 d2)"

definition MUX_Hex :: \<open>Hex \<Rightarrow> Hex \<Rightarrow> bit \<Rightarrow> Hex\<close> where [simp]:
  "MUX_Hex a b s \<equiv> case a of (Hex a1 b1 c1 d1)
                   \<Rightarrow> (case b of (Hex a2 b2 c2 d2)
                     \<Rightarrow> Hex (MUX a1 a2 s) (MUX b1 b2 s) (MUX c1 c2 s) (MUX d1 d2 s))"

lemma MUX_Hex_left [simp]: "MUX_Hex a b 0 = a"
  by (case_tac a; case_tac b) simp

lemma MUX_Hex_right [simp]: "MUX_Hex a b 1 = b"
  by (case_tac a; case_tac b) simp

section \<open>Logic Gates for Words\<close>

fun OR8 :: \<open>Hex \<Rightarrow> Hex \<Rightarrow> bit\<close> where
  "OR8 (Hex a1 b1 c1 d1) (Hex a2 b2 c2 d2) = OR (OR a1 a2) (OR (OR b1 b2) (OR (OR c1 c2) (OR d1 d2)))"

lemma OR8_zero: "OR8 (0 :: Hex) (0 :: Hex) = 0"
  by (simp add: zero_Hex_def)

lemma OR_zero_iff_zero: "OR a b = 0 \<longleftrightarrow> a = 0 \<and> b = 0"
  using NAND.elims by fastforce

lemma OR8_zero_implies_zero: "OR8 a b = 0 \<longrightarrow> a = 0 \<and> b = 0"
  by (smt (z3) Hex.exhaust OR8.simps OR_zero_iff_zero zero_Hex_def)

lemma OR8_zero_if_zero: "a = 0 \<and> b = 0 \<longrightarrow> OR8 a b = 0"
  by (simp add: zero_Hex_def)

lemma OR8_zero_iff_zero: "OR8 a b = 0 \<longleftrightarrow> a = 0 \<and> b = 0"
  using OR8_zero_implies_zero OR8_zero_if_zero by blast

fun ISZERO16 :: \<open>Word \<Rightarrow> bit\<close> where
  "ISZERO16 (Word a b c d) = NOT (OR (OR8 a b) (OR8 c d))"

lemma ISZERO16_check: "ISZERO16 (Word 0 0 0 0) = 1" by (simp add: OR8_zero)

lemma ISZERO16_implies_zero: "ISZERO16 (Word a b c d) = 1 \<longrightarrow> a = 0 \<and> b = 0 \<and> c = 0 \<and> d = 0"
  by (metis (full_types) ISZERO16.simps NOT_1 OR8_zero_iff_zero OR_1_0 OR_a_1 bit_not_one_iff) (* 111 ms *)

lemma ISZERO16_zero: "ISZERO16 (Word a b c d) = 1 \<longleftrightarrow> a = 0 \<and> b = 0 \<and> c = 0 \<and> d = 0"
  using ISZERO16_check ISZERO16_implies_zero by blast

fun NOT16 :: \<open>Word \<Rightarrow> Word\<close> where
  "NOT16 (Word a b c d) = Word (NOT_Hex a) (NOT_Hex b) (NOT_Hex c) (NOT_Hex d)"

lemma NOT16_zero: "NOT16 (Word 0 0 0 0) = Word XF XF XF XF"
  by (simp add: zero_Hex_def)

lemma NOT16_one: "NOT16 (Word 0 0 0 1) = (Word XF XF XF XE)"
  by (simp add: one_Hex_def zero_Hex_def)

lemma NOT16_NOT16: "NOT16 (NOT16 w) = w"
  using NOT_NOT_Hex by (case_tac w) auto

fun AND16 :: \<open>Word \<Rightarrow> Word \<Rightarrow> Word\<close> where
  "AND16 (Word a1 a2 a3 a4) (Word b1 b2 b3 b4)
   = Word (AND_Hex a1 b1) (AND_Hex a2 b2) (AND_Hex a3 b3) (AND_Hex a4 b4)"

lemma AND16_x_FFFF: "AND16 x (Word XF XF XF XF) = x"
  using AND_Hex_x_F by (case_tac x) auto

lemma AND16_FFFF_x: "AND16 (Word XF XF XF XF) x = x"
  using AND_Hex_F_x by (case_tac x) auto

fun OR16 :: \<open>Word \<Rightarrow> Word \<Rightarrow> Word\<close> where
  "OR16 (Word a1 a2 a3 a4) (Word b1 b2 b3 b4)
   = Word (OR_Hex a1 b1) (OR_Hex a2 b2) (OR_Hex a3 b3) (OR_Hex a4 b4)"

lemma NOT16_AND16_NOT16: "NOT16 (AND16 (NOT16 a) (NOT16 b)) = OR16 a b"
  by (case_tac a; case_tac b) (simp add: NOT_AND_NOT_Hex)

fun MUX16 :: \<open>Word \<Rightarrow> Word \<Rightarrow> bit \<Rightarrow> Word\<close> where
  "MUX16 (Word a1 b1 c1 d1) (Word a2 b2 c2 d2) s
   = Word (MUX_Hex a1 a2 s) (MUX_Hex b1 b2 s) (MUX_Hex c1 c2 s) (MUX_Hex d1 d2 s)"

lemma MUX16_left [simp]: "MUX16 a b 0 = a"
  using MUX_Hex_left by (case_tac a; case_tac b) simp

lemma MUX16_right [simp]: "MUX16 a b 1 = b"
  using MUX_Hex_right by (case_tac a; case_tac b) simp

section \<open>Arithmetic Gates for Hex and Words\<close>

(* Chained FULLADDERs returning the sum and its carry bit. *)

definition ADDER_Hex :: \<open>Hex \<Rightarrow> Hex \<Rightarrow> bit \<Rightarrow> Hex * bit\<close> where
"ADDER_Hex a b c \<equiv> (case a of (Hex a1 a2 a3 a4) \<Rightarrow> case b of (Hex b1 b2 b3 b4) \<Rightarrow>
(let (s4,c4) = FULLADDER a4 b4 c
in let (s3,c3) = FULLADDER a3 b3 c4
in let (s2,c2) = FULLADDER a2 b2 c3
in let (s1,c1) = FULLADDER a1 b1 c2
in (Hex s1 s2 s3 s4, c1)))"

lemma ADDER_Hex_simps [simp]: "ADDER_Hex (Hex a1 a2 a3 a4) (Hex b1 b2 b3 b4) c
= (let (s4,c4) = FULLADDER a4 b4 c
in let (s3,c3) = FULLADDER a3 b3 c4
in let (s2,c2) = FULLADDER a2 b2 c3
in let (s1,c1) = FULLADDER a1 b1 c2
in (Hex s1 s2 s3 s4, c1))"
  by (simp add: ADDER_Hex_def)

lemma ADDER_Hex_simps2: "ADDER_Hex (Hex a1 a2 a3 a4) (Hex b1 b2 b3 b4) c
= (Hex (fst (FULLADDER a1 b1 (snd (FULLADDER a2 b2 (snd (FULLADDER a3 b3 (snd (FULLADDER a4 b4 c))))))))
       (fst (FULLADDER a2 b2 (snd (FULLADDER a3 b3 (snd (FULLADDER a4 b4 c))))))
       (fst (FULLADDER a3 b3 (snd (FULLADDER a4 b4 c))))
       (fst (FULLADDER a4 b4 c)),
  (snd (FULLADDER a1 b1 (snd (FULLADDER a2 b2 (snd (FULLADDER a3 b3 (snd (FULLADDER a4 b4 c)))))))))"
  by (simp add: case_prod_beta)

lemma ADDER_Hex_alias: "(s4,c4) = FULLADDER a4 b4 c \<and> (s3,c3) = FULLADDER a3 b3 c4
    \<and> (s2,c2) = FULLADDER a2 b2 c3 \<and> (s1,c1) = FULLADDER a1 b1 c2 
    \<longrightarrow> (Hex s1 s2 s3 s4, c1) = ADDER_Hex (Hex a1 a2 a3 a4) (Hex b1 b2 b3 b4) c"
  by (smt (verit, ccfv_threshold) ADDER_Hex_simps prod.simps(2))

lemma ADDER_Hex_0b0: "ADDER_Hex (Hex 0 0 0 0) b 0 = (b, 0)"
  using FULLADDER_0b0 by (case_tac b) auto

lemma ADDER_Hex_a00: "ADDER_Hex a (Hex 0 0 0 0) 0 = (a, 0)"
  using FULLADDER_a00 by (case_tac a) auto

(* Brute force check all situations. It's not clever, but the readable Isar proof is too long
   and about as interesting as Homer's catalogue of ships.

   Although this suffices for now, it seems that there's some logic which could be refactored
   out of ADDER16_check's proof to improve the proof-time for this theorem.

   But, hey, it's only 31 cases as opposed to 1024, so that's good, right? *)
lemma ADDER_Hex_check4: "(s,c) = ADDER_Hex a b 0 \<longrightarrow> (Hex_to_nat a) + (Hex_to_nat b) = 16*(bit_to_nat c) + (Hex_to_nat s)"
  apply (case_tac a; case_tac x1; case_tac x2; case_tac x3; case_tac x4)
  apply (simp add: ADDER_Hex_0b0)
  apply (case_tac b; case_tac x1a; case_tac x2a; case_tac x3a; case_tac x4a; simp)+
  done

corollary ADDER_Hex_check2: "(s,0 :: bit) = ADDER_Hex a b 0 \<longrightarrow> (Hex_to_nat a) + (Hex_to_nat b) = (Hex_to_nat s)"
  by (simp add: ADDER_Hex_check4)

lemma ADDER_Hex_check2b: "(s,c :: bit) = ADDER_Hex a b 1
  \<longrightarrow> (Hex_to_nat a) + (Hex_to_nat b) + (bit_to_nat 1) = 16*(bit_to_nat c) + (Hex_to_nat s)"
  apply (case_tac a; case_tac x1; case_tac x2; case_tac x3; case_tac x4)
  apply (case_tac b)
  apply (case_tac b; case_tac x1a; case_tac x2a; case_tac x3a; case_tac x4a; simp)+
  done

theorem ADDER_Hex_check_carry: "(s, c :: bit) = ADDER_Hex a b c2 \<longrightarrow>
  (Hex_to_nat a) + (Hex_to_nat b) + (bit_to_nat c2) = 16*(bit_to_nat c) + (Hex_to_nat s)"
proof -
  have "\<forall>b h ha hb. bit_to_nat 1 + (Hex_to_nat h + Hex_to_nat hb) = 16*bit_to_nat b + Hex_to_nat ha
    \<or> (ha, b) \<noteq> ADDER_Hex h hb 1"
    using ADDER_Hex_check2b by fastforce
  moreover have "0 = c2 \<longrightarrow> Hex_to_nat s + 16*bit_to_nat c = bit_to_nat c2 + (Hex_to_nat a + Hex_to_nat b)
    \<or> ((s, c) = ADDER_Hex a b c2
     \<longrightarrow> Hex_to_nat a + Hex_to_nat b + bit_to_nat c2 = 16 * bit_to_nat c + Hex_to_nat s)"
    by (simp add: ADDER_Hex_check4)
  ultimately show ?thesis
    by fastforce
qed

corollary ADDER_Hex_check3: "(s,1 :: bit) = ADDER_Hex a b 0 \<longrightarrow> (Hex_to_nat a) + (Hex_to_nat b) = 16 + (Hex_to_nat s)"
  using ADDER_Hex_check_carry by fastforce

corollary ADDER_Hex_check_carry2: "(s,0 :: bit) = ADDER_Hex a b 1 \<longrightarrow> (Hex_to_nat a) + (Hex_to_nat b) + 1 = (Hex_to_nat s)"
  using ADDER_Hex_check_carry by fastforce

corollary ADDER_Hex_check_carry3: "(s,1 :: bit) = ADDER_Hex a b 1 \<longrightarrow> (Hex_to_nat a) + (Hex_to_nat b) + 1 = 16 + (Hex_to_nat s)"
  using ADDER_Hex_check_carry by fastforce

corollary ADDER_Hex_check: "Hex_to_nat (fst (ADDER_Hex a b 0)) = ((Hex_to_nat a) + (Hex_to_nat b)) mod 16"
proof - (* 5 ms *)
  have "Hex_to_nat a + Hex_to_nat b = 16 * bit_to_nat (snd (ADDER_Hex a b 0)) + Hex_to_nat (fst (ADDER_Hex a b 0))"
    by (simp add: ADDER_Hex_check4)
  then show ?thesis
    by simp
qed

corollary ADDER_Hex_small: "(Hex_to_nat a) + (Hex_to_nat b) < 16 \<longrightarrow> (s,0 :: bit) = ADDER_Hex a b 0
  \<longrightarrow> (Hex_to_nat a) + (Hex_to_nat b) = (Hex_to_nat s)"
  using ADDER_Hex_check2 by blast

theorem ADDER_Hex_comm: "ADDER_Hex a b c = ADDER_Hex b a c"
  by (case_tac a; case_tac b) (simp add: FULLADDER_comm)

(* Add two words together, does not signal overflow or underflow, discards carry bit. *)
fun ADDER16 :: \<open>Word \<Rightarrow> Word \<Rightarrow> Word\<close> where
  "ADDER16 (Word a1 a2 a3 a4) (Word b1 b2 b3 b4) = (let (s4,c4) = ADDER_Hex a4 b4 0
  in let (s3,c3) = ADDER_Hex a3 b3 c4
  in let (s2,c2) = ADDER_Hex a2 b2 c3
  in let (s1,c1) = ADDER_Hex a1 b1 c2
  in (Word s1 s2 s3 s4))"

lemma ADDER16_alias: "(s4,c4) = ADDER_Hex a4 b4 0 \<and> (s3,c3) = ADDER_Hex a3 b3 c4
  \<and> (s2,c2) = ADDER_Hex a2 b2 c3 \<and> (s1,c1) = ADDER_Hex a1 b1 c2
 \<longrightarrow> ADDER16 (Word a1 a2 a3 a4) (Word b1 b2 b3 b4) = (Word s1 s2 s3 s4)"
  by (metis (no_types, lifting) ADDER16.simps split_conv)

lemma ADDER16_0b: "ADDER16 (Word 0 0 0 0) b = b"
  by (case_tac b) (simp add: ADDER_Hex_0b0 zero_Hex_def)

lemma ADDER16_a0: "ADDER16 a (Word 0 0 0 0) = a"
  by (case_tac a) (simp add: ADDER_Hex_a00 zero_Hex_def)

lemma ADDER16_check: "Word_to_nat (ADDER16 a b) = ((Word_to_nat a) + (Word_to_nat b)) mod 65536"
proof (cases a)
  case A: (Word a1 a2 a3 a4)
  then show ?thesis
  proof (cases b)
    case B: (Word b1 b2 b3 b4)
    let ?x4 = "ADDER_Hex a4 b4 0"
    let ?c4 = "snd ?x4"
    let ?s4 = "fst ?x4"
    let ?x3 = "ADDER_Hex a3 b3 ?c4"
    let ?c3 = "snd ?x3"
    let ?s3 = "fst ?x3"
    let ?x2 = "ADDER_Hex a2 b2 ?c3"
    let ?c2 = "snd ?x2"
    let ?s2 = "fst ?x2"
    let ?x1 = "ADDER_Hex a1 b1 ?c2"
    let ?c1 = "snd ?x1"
    let ?s1 = "fst ?x1"
    have A1: "ADDER16 a b = Word ?s1 ?s2 ?s3 ?s4" by (simp add: A B split_beta)
    moreover have A2: "Word_to_nat a = (Hex_to_nat a4) + 16*(Hex_to_nat a3) + 256*(Hex_to_nat a2) + 4096*(Hex_to_nat a1)"
      by (simp add: A)
    moreover have A3: "Word_to_nat b = (Hex_to_nat b4) + 16*(Hex_to_nat b3) + 256*(Hex_to_nat b2) + 4096*(Hex_to_nat b1)"
      by (simp add: B)
    moreover have AA4: "(Hex_to_nat a4) + (Hex_to_nat b4) = (Hex_to_nat ?s4) + 16*(bit_to_nat ?c4)"
      by (metis ADDER_Hex_check4 add.commute prod.collapse)
    moreover have AA3: "(Hex_to_nat a3) + (Hex_to_nat b3) + (bit_to_nat ?c4)
                   = (Hex_to_nat ?s3) + 16*(bit_to_nat ?c3)"
      by (metis ADDER_Hex_check_carry add.commute surjective_pairing)
    moreover have AA2: "(Hex_to_nat a2) + (Hex_to_nat b2) + (bit_to_nat ?c3)
                   = (Hex_to_nat ?s2) + 16*(bit_to_nat ?c2)"
      by (metis ADDER_Hex_check_carry add.commute prod.exhaust_sel)
    moreover have AA1: "(Hex_to_nat a1) + (Hex_to_nat b1) + (bit_to_nat ?c2)
                   = (Hex_to_nat ?s1) + 16*(bit_to_nat ?c1)"
      by (metis ADDER_Hex_check_carry add.commute prod.exhaust_sel)
    moreover have AA5: "(Hex_to_nat a2) + (Hex_to_nat b2) + (bit_to_nat ?c3)
                       + (16 :: nat)*((Hex_to_nat a1) + (Hex_to_nat b1))
                  = (Hex_to_nat ?s2)
                    + (16 :: nat)*((Hex_to_nat ?s1) 
                                   + (16 :: nat)*(bit_to_nat ?c1))"
      using AA1 AA2 add.commute add.left_commute distrib_left_numeral by auto
    ultimately have A4: "(Hex_to_nat a4) + (Hex_to_nat b4) 
                    + (16 :: nat)*((Hex_to_nat a3) + (Hex_to_nat b3)
                          + (16 :: nat)*((Hex_to_nat a2) + (Hex_to_nat b2)
                                + (16 :: nat)*((Hex_to_nat a1) + (Hex_to_nat b1))))
                  = (Hex_to_nat ?s4)
                   + (16 :: nat)*((Hex_to_nat ?s3)
                         + (16 :: nat)*((Hex_to_nat ?s2) 
                                + (16 :: nat)*((Hex_to_nat ?s1) 
                                      + (16 :: nat)*(bit_to_nat ?c1))))"
      by auto
    have "(Word_to_nat a)
             + (Hex_to_nat b4) + 16*(Hex_to_nat b3)
             + 256*(Hex_to_nat b2)
             + 4096*(Hex_to_nat b1)
           = (Hex_to_nat ?s4)
             + 16*(Hex_to_nat ?s3)
             + 256*(Hex_to_nat ?s2)
             + 4096*((Hex_to_nat ?s1) + 16*(bit_to_nat ?c1))"
      using A4 nat_distrib A Word_to_nat.simps by auto
    then have "(Word_to_nat a) + (Word_to_nat b) = (Word_to_nat (ADDER16 a b)) + 4096*16*(bit_to_nat ?c1)"
      using A1 A3 add.assoc by simp
    then have "(((Word_to_nat a) + (Word_to_nat b)) :: nat) mod (65536 :: nat)
               = (((Word_to_nat (ADDER16 a b)) + (4096 :: nat)*16*(bit_to_nat ?c1)) :: nat) mod (65536 :: nat)"
      by force
    then have "((Word_to_nat a) + (Word_to_nat b)) mod 65536
               = (Word_to_nat (ADDER16 a b)) mod 65536"
      using Euclidean_Rings.euclidean_semiring_cancel_class.mod_mult_self2
      by auto
    then have "((Word_to_nat a) + (Word_to_nat b)) mod 65536
               = (Word_to_nat (ADDER16 a b))"
      using Word_to_nat_mod65536 by auto
    then show ?thesis by simp
  qed
qed

theorem ADDER16_comm: "ADDER16 x y = ADDER16 y x"
  by (case_tac x; case_tac y) (simp add: ADDER_Hex_comm)

lemma Word_to_nat_injective: "Word_to_nat a = Word_to_nat b \<Longrightarrow> a = b"
  by (metis Word_to_nat_to_Word)

theorem ADDER16_assoc: "ADDER16 a (ADDER16 b c) = ADDER16 (ADDER16 a b) c"
proof-
  have "Word_to_nat (ADDER16 a (nat_to_Word (Word_to_nat (ADDER16 b c)))) = ((Word_to_nat a) + (((Word_to_nat b) + (Word_to_nat c)) mod 65536)) mod 65536"
    by (metis ADDER16_check Word_to_nat_to_Word)
  then have "Word_to_nat (ADDER16 a (ADDER16 b c)) = ((Word_to_nat a) + (Word_to_nat b) + (Word_to_nat c)) mod 65536"
    by (metis Word_to_nat_to_Word ab_semigroup_add_class.add_ac(1) mod_add_right_eq)
  moreover have "Word_to_nat (ADDER16 (ADDER16 a b) c) = ((Word_to_nat a) + (Word_to_nat b) + (Word_to_nat c)) mod 65536"
  proof-
    have "Word_to_nat (ADDER16 (ADDER16 a b) c) = ((Word_to_nat (ADDER16 a b)) + (Word_to_nat c)) mod 65536"
      using ADDER16_check by simp
    moreover have "(Word_to_nat (ADDER16 a b)) = ((Word_to_nat a) + (Word_to_nat b)) mod 65536"
      using ADDER16_check by simp
    moreover have "((((Word_to_nat a) + (Word_to_nat b)) mod 65536) + z) mod 65536 = ((Word_to_nat a) + (Word_to_nat b) + z) mod 65536"
      by presburger
    ultimately show ?thesis by presburger
  qed
  ultimately have "Word_to_nat (ADDER16 a (ADDER16 b c)) = Word_to_nat (ADDER16 (ADDER16 a b) c)"
    by presburger
  then show ?thesis using Word_to_nat_injective by simp
qed

lemma FULLADDER_x_not_x: "FULLADDER x (NOT x) 0 = (1, 0)"
  by (metis FULLADDER_010 FULLADDER_100 NOT_0 NOT_1 bit.exhaust)

lemma ADDER_Hex_x_not_x_0: "ADDER_Hex x (NOT_Hex x) 0 = (XF,0)"
   using FULLADDER_x_not_x by (case_tac x) force

lemma ADDER16_x_not_x: "ADDER16 x (NOT16 x) = (Word XF XF XF XF)"
  using ADDER_Hex_x_not_x_0 ADDER16_alias by (case_tac x) auto

fun INC16 :: \<open>Word \<Rightarrow> Word\<close> where
  "INC16 a = ADDER16 a (Word 0 0 0 1)"

lemma INC16_fffe: "INC16 (Word XF XF XF XE) = (Word XF XF XF XF)"
  by (simp add: ADDER16_a0 one_Hex_def zero_Hex_def)

lemma INC16_ffff: "INC16 (Word XF XF XF XF) = (Word 0 0 0 0)"
  by (simp add: one_Hex_def zero_Hex_def)

lemma "INC16 (ADDER16 x (NOT16 x)) = Word 0 0 0 0"
  using ADDER16_x_not_x INC16_ffff by auto

lemma INC_swaps_ADD16: "y = (Word XF XF XF XF) \<longrightarrow> ADDER16 x (INC16 y) = INC16 (ADDER16 x y)"
  using ADDER16_assoc INC16.simps by presburger

section \<open>Arithmetic Logical Unit\<close>

fun NEGATE16 :: \<open>Word \<Rightarrow> Word\<close> where
  "NEGATE16 w = INC16 (NOT16 w)"

lemma NEGATE_swap_inc: "ADDER16 (Word 0 0 0 1) (NOT16 x) = NEGATE16 x"
  by (simp add: ADDER16_comm)

lemma NEGATE16_zero: "NEGATE16 (Word 0 0 0 0) = (Word 0 0 0 0)"
  by (metis (mono_tags, lifting) INC16_ffff NEGATE16.elims NOT16.simps NOT_0 NOT_Hex.simps zero_Hex_def)

lemma NEGATE16_one: "NEGATE16 (Word 0 0 0 1) = (Word XF XF XF XF)"
  using INC16_fffe NOT16_one by auto

lemma INC_negate_one: "INC16 (NEGATE16 (Word 0 0 0 1)) = Word 0 0 0 0"
  using INC16_ffff NEGATE16_one by presburger

fun SUB16 :: \<open>Word \<Rightarrow> Word \<Rightarrow> Word\<close> where
  "SUB16 x y = ADDER16 x (NEGATE16 y)"

lemma SUB16_x_x: "SUB16 x x = (Word 0 0 0 0)"
  using ADDER16_assoc ADDER16_x_not_x INC_negate_one NEGATE16_one by auto

fun DEC16 :: \<open>Word \<Rightarrow> Word\<close> where
  "DEC16 x = SUB16 x (Word 0 0 0 1)"

lemma DEC_is_add_neg: "DEC16 x = ADDER16 x (NEGATE16 (Word 0 0 0 1))" by simp 

lemma DEC_as_minus_one_plus_y: "ADDER16 (NEGATE16 (Word 0 0 0 1)) x = DEC16 x" 
  using ADDER16_comm by auto

lemma NEGATE_iff_sums_to_zero: "y = NEGATE16 x \<longleftrightarrow> ADDER16 x y = (Word 0 0 0 0)"
  by (metis (no_types) ADDER16_0b ADDER16_assoc SUB16.elims SUB16_x_x)

fun ZERO_OUT_WORD :: \<open>Word \<Rightarrow> bit \<Rightarrow> Word\<close> where
  "ZERO_OUT_WORD w zr = MUX16 w (Word 0 0 0 0) zr"

lemma ZERO_OUT_WORD_isZero: "ISZERO16 (ZERO_OUT_WORD w 1) = 1"
  using ISZERO16_zero by auto

fun NOT_WORD :: \<open>Word \<Rightarrow> bit \<Rightarrow> Word\<close> where
  "NOT_WORD w ng = MUX16 w (NOT16 w) ng"

fun ZERO_OR_NOT :: \<open>Word \<Rightarrow> bit \<Rightarrow> bit \<Rightarrow> Word\<close> where
  "ZERO_OR_NOT w zr ng = (NOT_WORD (ZERO_OUT_WORD w zr) ng)"

lemma ZERO_OR_NOT_w00: "ZERO_OR_NOT w 0 0 = w" by simp

lemma ZERO_OR_NOT_w01: "ZERO_OR_NOT w 0 1 = NOT16 w" by simp

lemma ZERO_OR_NOT_w10: "ZERO_OR_NOT w 1 0 = (Word 0 0 0 0)" by simp

lemma ZERO_OR_NOT_w11 [simp]: "ZERO_OR_NOT w 1 1 = (Word XF XF XF XF)"
  using NOT16_zero by auto

fun ADDER16_OR_AND16 :: \<open>Word \<Rightarrow> Word \<Rightarrow> bit \<Rightarrow> Word\<close> where
  "ADDER16_OR_AND16 a b f = MUX16 (AND16 a b) (ADDER16 a b) f"

lemma ADDER_OR_AND_ab1: "ADDER16_OR_AND16 a b 1 = ADDER16 a b"
  by simp

lemma ADDER_OR_AND_ab0: "ADDER16_OR_AND16 a b 0 = AND16 a b"
  by simp

(* The ALU operation without transforming the output. *)
fun ALU_op :: \<open>Word \<Rightarrow> Word \<Rightarrow> bit \<Rightarrow> bit \<Rightarrow> bit \<Rightarrow> bit \<Rightarrow> bit \<Rightarrow> Word\<close> where
  "ALU_op x y zx nx zy ny f = (ADDER16_OR_AND16 (ZERO_OR_NOT x zx nx) (ZERO_OR_NOT y zy ny) f)"

lemma ALU_11111: "ALU_op x y 1 1 1 1 1 = Word XF XF XF XE"
  using ADDER_OR_AND_ab1 ZERO_OR_NOT_w11 by auto

lemma ALU_op_00001: "ALU_op x y 0 0 0 0 1 = ADDER16 x y"
  by simp

lemma ALU_op_00110: "ALU_op x y 0 0 1 1 0 = x"
  using AND16_x_FFFF NOT16_zero by auto

lemma ALU_op_00111: "ALU_op x y 0 0 1 1 1 = DEC16 x"
  using ADDER_OR_AND_ab1 ALU_op.simps DEC_is_add_neg NEGATE16_one ZERO_OR_NOT_w00 ZERO_OR_NOT_w11
  by presburger

lemma ALU_op_01001: "ALU_op x y 0 1 0 0 1 = ADDER16 (NOT16 x) y"
  by simp

lemma ALU_op_01111: "ALU_op x y 0 1 1 1 1 = DEC16 (NOT16 x)"
  using INC16_fffe NOT16_one by auto

lemma NOT_DEC_NOT_is_INC: "NOT16 (DEC16 (NOT16 x)) = INC16 x"
  by (metis (no_types, opaque_lifting) ADDER16_0b ADDER16_assoc DEC16.elims DEC_as_minus_one_plus_y
      INC16.elims NEGATE16.elims SUB16.elims SUB16_x_x)

lemma ALU_op_11000: "ALU_op x y 1 1 0 0 0 = y"
  using AND16_FFFF_x NOT16_zero by auto

lemma ALU_op_11001: "ALU_op x y 1 1 0 0 1 = DEC16 y"
proof-
  have "ALU_op x y 1 1 0 0 1 = ADDER16 (NOT16 (Word 0 0 0 0)) y" by auto
  then show ?thesis
    by (metis (no_types, lifting) ADDER16.simps ADDER16_a0 ADDER_Hex_simps DEC_as_minus_one_plus_y
        FULLADDER_010 FULLADDER_100 INC16.simps NEGATE16.simps NOT16.simps NOT_0 NOT_1 NOT_Hex.simps
        one_Hex_def zero_Hex_def)
qed

fun ALU :: \<open>Word \<Rightarrow> Word \<Rightarrow> bit \<Rightarrow> bit \<Rightarrow> bit \<Rightarrow> bit \<Rightarrow> bit \<Rightarrow> bit \<Rightarrow> Word * bit * bit\<close> where
  "ALU x y zx nx zy ny f no = (let sym = ALU_op x y zx nx zy ny f
  in let output = MUX16 sym (NOT16 sym) no
  in (output, ISZERO16 output, sign_bit output))"

text \<open>To prove correctness of the ALU implementation, we should check each of the 19 cases for the
possible outputs.\<close>

theorem ALU_101010: "ALU x y 1 0 1 0 1 0 = (Word 0 0 0 0, 1, 0)"
  by (simp add: zero_Hex_def)

theorem ALU_111111: "ALU x y 1 1 1 1 1 1 = (Word 0 0 0 1, 0, 0)"
  by (simp add: one_Hex_def zero_Hex_def)

theorem ALU_111010: "ALU x y 1 1 1 0 1 0 = (Word XF XF XF XF, 0, 1)"
  using ADDER16_a0 MUX16_left ZERO_OR_NOT_w11 by auto

theorem ALU_001100: "ALU x y 0 0 1 1 0 0 = (x, ISZERO16 x, sign_bit x)"
  using ALU_op_00110 by auto

theorem ALU_110000: "ALU x y 1 1 0 0 0 0 = (y, ISZERO16 y, sign_bit y)"
  using ALU_op_11000 by auto

theorem ALU_001101: "ALU x y 0 0 1 1 0 1 = (NOT16 x, ISZERO16 (NOT16 x), sign_bit (NOT16 x))"
  by (metis ALU.simps ALU_op_00110 MUX16_right)

theorem ALU_110001: "ALU x y 1 1 0 0 0 1 = (NOT16 y, ISZERO16 (NOT16 y), sign_bit (NOT16 y))"
  by (metis ALU.simps ALU_op_11000 MUX16_right)

lemma NOT_DEC_is_NEGATE: "NOT16 (DEC16 x) = NEGATE16 x"
  by (metis NEGATE16.simps NOT16_NOT16 NOT_DEC_NOT_is_INC)

theorem ALU_001111: "ALU x y 0 0 1 1 1 1 = (NEGATE16 x, ISZERO16 (NEGATE16 x), sign_bit (NEGATE16 x))"
  by (metis ALU.simps ALU_op_00111 MUX16_right NOT_DEC_is_NEGATE)

theorem ALU_110011: "ALU x y 1 1 0 0 1 1 = (NEGATE16 y, ISZERO16 (NEGATE16 y), sign_bit (NEGATE16 y))"
  by (smt (z3) ALU.simps ALU_op_11001 MUX16_right NEGATE16.simps NOT16_NOT16 NOT_DEC_NOT_is_INC)

theorem ALU_011111: "ALU x y 0 1 1 1 1 1 = (INC16 x, ISZERO16 (INC16 x), sign_bit (INC16 x))"
  by (metis ALU.simps ALU_op_01111 MUX16_right NOT_DEC_NOT_is_INC)

theorem ALU_110111: "ALU x y 1 1 0 1 1 1 = (INC16 y, ISZERO16 (INC16 y), sign_bit (INC16 y))"
proof -
  have "ALU_op x y 1 1 0 1 1 = DEC16 (NOT16 y)"
    using DEC_as_minus_one_plus_y NEGATE16_one ZERO_OR_NOT_w11 by force
  then show ?thesis
    by (smt (z3) ALU.simps MUX16_right NOT_DEC_NOT_is_INC)
qed

theorem ALU_001110: "ALU x y 0 0 1 1 1 0 = (DEC16 x, ISZERO16 (DEC16 x), sign_bit (DEC16 x))"
  by (metis ALU.simps ALU_op_00111 MUX16_left)

theorem ALU_110010: "ALU x y 1 1 0 0 1 0 = (DEC16 y, ISZERO16 (DEC16 y), sign_bit (DEC16 y))"
  by (metis ALU.simps ALU_op_11001 MUX16_left)

theorem ALU_000010: "ALU x y 0 0 0 0 1 0 = (ADDER16 x y, ISZERO16 (ADDER16 x y), sign_bit (ADDER16 x y))"
  by (smt (z3) ADDER_OR_AND_ab1 ALU.simps ALU_op.simps MUX16_left NOT_WORD.simps 
      ZERO_OR_NOT.simps ZERO_OUT_WORD.simps)

lemma ADD_NOT_x_y: "NOT16 (ADDER16 (NOT16 x) y) = SUB16 x y"
proof -
  have "\<forall>w wa. ADDER16 (SUB16 w w) wa = wa"
    using ADDER16_0b SUB16_x_x by presburger
  then show ?thesis
    by (smt (z3) ADDER16_0b ADDER16_assoc ADDER16_comm ADDER16_x_not_x SUB16.simps SUB16_x_x)
qed

theorem ALU_010011: "ALU x y 0 1 0 0 1 1 = (SUB16 x y, ISZERO16 (SUB16 x y), sign_bit (SUB16 x y))"
  by (metis ADD_NOT_x_y ALU.simps ALU_op_01001 MUX16_right)

theorem ALU_000111: "ALU x y 0 0 0 1 1 1 = (SUB16 y x, ISZERO16 (SUB16 y x), sign_bit (SUB16 y x))"
  using ADDER16_comm ALU_010011 by auto

theorem ALU_000000: "ALU x y 0 0 0 0 0 0 = (AND16 x y, ISZERO16 (AND16 x y), sign_bit (AND16 x y))"
  by (metis ADDER_OR_AND_ab0 ALU.simps ALU_op.simps MUX16_left NOT_WORD.simps
      ZERO_OR_NOT.simps ZERO_OUT_WORD.simps)

theorem ALU_010101: "ALU x y 0 1 0 1 0 1 = (OR16 x y, ISZERO16 (OR16 x y), sign_bit (OR16 x y))"
proof - (* 81 ms *)
  have "\<forall>b w ba. ZERO_OR_NOT w ba b = NOT_WORD (MUX16 w (Word 0 0 0 0) ba) b"
    using ZERO_OR_NOT.simps ZERO_OUT_WORD.simps by presburger
  moreover have "\<forall>w. NOT16 w = NOT_WORD (MUX16 w (Word 0 0 0 0) 0) 1"
    by simp
  ultimately show ?thesis
    by (smt (z3) ADDER16_OR_AND16.simps ALU.simps ALU_op.simps MUX16_left NOT16_AND16_NOT16
        NOT_WORD.simps)
qed

end