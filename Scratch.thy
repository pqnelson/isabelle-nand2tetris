theory Scratch
  imports Main "~~/src/HOL/Library/Z2" HOL.Sledgehammer HOL.Nitpick
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
proof (cases b)
  assume "b = 0"
  thus ?thesis using NAND_a_0 NAND_0_b by auto
next
  assume A1: "b = 1"
  have "NAND a 1 = NAND 1 a" by (case_tac a) auto
  thus ?thesis using A1 by simp
qed

definition NOT :: \<open>bit \<Rightarrow> bit\<close>
  where [simp]: \<open>NOT a \<equiv> (NAND a a)\<close>

lemma NOT_0 [simp]: "NOT (0::bit) \<equiv> (1::bit)"
  by simp

lemma NOT_1 [simp]: "NOT (1::bit) \<equiv> (0::bit)"
  by simp

theorem NOT_NOT: "NOT (NOT a) = a"
  by (case_tac a) auto

definition AND :: \<open>bit \<Rightarrow> bit \<Rightarrow> bit\<close>
  where [simp]: \<open>AND a b \<equiv> NAND (NAND a b) (NAND a b)\<close>

lemma AND_0_0: "AND (0::bit) (0::bit) \<equiv> (0::bit)"
  by simp

lemma AND_0_1: "AND (0::bit) (1::bit) \<equiv> (0::bit)"
  by simp

lemma AND_1_0: "AND (1::bit) (0::bit) \<equiv> (0::bit)"
  by simp

lemma AND_1_1: "AND (1::bit) (1::bit) \<equiv> (1::bit)"
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
proof (cases b)
  case zero
  thus ?thesis using AND_0_b AND_a_0 by simp
next
  case one
  thus ?thesis using AND_1_b AND_a_1 by simp
qed

\<comment>\<open>We can prove that NAND really is just "NOT AND"!\<close>
lemma NOT_AND_is_NAND: "NOT (AND a b) = NAND a b"
proof (cases a)
  case zero
  thus ?thesis by simp
next
  case one
  thus ?thesis by (case_tac b) auto
qed

definition OR :: \<open>bit \<Rightarrow> bit \<Rightarrow> bit\<close>
  where [simp]: \<open>OR a b \<equiv> NAND (NOT a) (NOT b)\<close>

lemma OR_0_0: "OR (0::bit) (0::bit) \<equiv> (0::bit)"
  by simp

lemma OR_0_1: "OR (0::bit) (1::bit) \<equiv> (1::bit)"
  by simp

lemma OR_1_0: "OR (1::bit) (0::bit) \<equiv> (1::bit)"
  by simp

lemma OR_1_1: "OR (1::bit) (1::bit) \<equiv> (1::bit)"
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

theorem de_Morgan_gate1: "NOT (AND a b) = OR (NOT a) (NOT b)"
proof (cases a)
  case zero
  thus ?thesis by simp
next
  case one
  thus ?thesis using AND_1_b OR_0_b by simp
qed

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
  where [simp]: \<open>MUX a b s \<equiv> NAND (NAND a (NOT s)) (NAND b s)\<close>

theorem MUX_left [simp]: "MUX a b 0 = a"
  by (case_tac a) auto

theorem MUX_right [simp]: "MUX a b 1 = b"
  by (case_tac b) auto

(* MUX_left and right suffice for specifying its behaviour. *)
declare MUX_def[simp del]

lemma MUX_alt: "MUX a b s = OR (AND a (NOT s)) (AND b s)"
proof (cases s)
  assume A1: "s = 0"
  have "OR (AND a (NOT 0)) (AND b 0) = a" using OR_a_0 AND_a_1 by simp
  thus ?thesis using A1 MUX_left by simp
next
  assume A1: "s = 1"
  have "OR (AND a (NOT 1)) (AND b 1) = b" using OR_0_b AND_a_1 by simp
  thus ?thesis using A1 MUX_right by simp
qed

(* The implementation of DMUX is not as important as its defining properties,
which we prove immediately and add to the simplification tactic. *)
definition DMUX :: \<open>bit \<Rightarrow> bit \<Rightarrow> (bit * bit)\<close>
  where \<open>DMUX i s \<equiv> (AND i (NOT s), AND i s)\<close>

lemma DMUX_left [simp]: "DMUX i 0 = (i, 0)"
proof
  show "fst (DMUX i 0) = fst(i,0)" using AND_a_1 by (simp add: DMUX_def)
  show "snd (DMUX i 0) = snd (i, 0)" by (simp add: DMUX_def)
qed

lemma DMUX_right [simp]: "DMUX i 1 = (0, i)"
proof
  show "fst (DMUX i 1) = fst(0,i)" by (simp add: DMUX_def)
  show "snd (DMUX i 1) = snd (0, i)" using AND_a_1 by (simp add: DMUX_def)
qed

(* Only 9 NAND gates are needed for the FULLADDER, returns (sum, carry). *)
definition FULLADDER :: \<open>bit \<Rightarrow> bit \<Rightarrow> bit \<Rightarrow> (bit * bit)\<close>
  where \<open>FULLADDER a b c \<equiv> let nab = NAND a b 
in let sab = NAND (NAND b nab) (NAND a nab)
in let scab = NAND sab c
in (NAND (NAND scab sab) (NAND scab c), NAND nab scab)\<close>

value "FULLADDER a b c"
value "FULLADDER 1 0 1"

lemma FULLADDER_000 [simp]: "FULLADDER 0 0 0 = (0, 0)"
proof
  show "(fst (FULLADDER 0 0 0)) = fst(0,0)" by (simp add: FULLADDER_def)
  show "(snd (FULLADDER 0 0 0)) = snd(0,0)" by (simp add: FULLADDER_def)
qed

lemma FULLADDER_001 [simp]: "FULLADDER 0 0 1 = (1, 0)"
proof
  show "(fst (FULLADDER 0 0 1)) = fst(1,0)" by (simp add: FULLADDER_def)
  show "(snd (FULLADDER 0 0 1)) = snd(1,0)" by (simp add: FULLADDER_def)
qed

lemma FULLADDER_010 [simp]: "FULLADDER 0 1 0 = (1, 0)"
proof
  show "(fst (FULLADDER 0 1 0)) = fst(1,0)" by (simp add: FULLADDER_def)
  show "(snd (FULLADDER 0 1 0)) = snd(1,0)" by (simp add: FULLADDER_def)
qed

lemma FULLADDER_011 [simp]: "FULLADDER 0 1 1 = (0, 1)"
proof
  show "(fst (FULLADDER 0 1 1)) = fst(0,1)" by (simp add: FULLADDER_def)
  show "(snd (FULLADDER 0 1 1)) = snd(0,1)" by (simp add: FULLADDER_def)
qed

lemma FULLADDER_100 [simp]: "FULLADDER 1 0 0 = (1, 0)"
proof
  show "(fst (FULLADDER 1 0 0)) = fst(1,0)" by (simp add: FULLADDER_def)
  show "(snd (FULLADDER 1 0 0)) = snd(1,0)" by (simp add: FULLADDER_def)
qed

lemma FULLADDER_101 [simp]: "FULLADDER 1 0 1 = (0, 1)"
proof
  show "(fst (FULLADDER 1 0 1)) = fst(0,1)" by (simp add: FULLADDER_def)
  show "(snd (FULLADDER 1 0 1)) = snd(0,1)" by (simp add: FULLADDER_def)
qed

lemma FULLADDER_110 [simp]: "FULLADDER 1 1 0 = (0, 1)"
proof
  show "(fst (FULLADDER 1 1 0)) = fst(0,1)" by (simp add: FULLADDER_def)
  show "(snd (FULLADDER 1 1 0)) = snd(0,1)" by (simp add: FULLADDER_def)
qed

lemma FULLADDER_111 [simp]: "FULLADDER 1 1 1 = (1, 1)"
proof
  show "(fst (FULLADDER 1 1 1)) = fst(1,1)" by (simp add: FULLADDER_def)
  show "(snd (FULLADDER 1 1 1)) = snd(1,1)" by (simp add: FULLADDER_def)
qed

lemma FULLADDER_00c: "FULLADDER 0 0 c = (c,0)"
  by (metis (full_types) FULLADDER_000 FULLADDER_001 bit.exhaust) 

lemma FULLADDER_0bc: "FULLADDER 0 b c = (XOR b c,AND b c)"
proof -
  have "1 = b \<and> 1 = c \<longrightarrow> FULLADDER 0 b c = (XOR b c, AND b c)"
    by auto
  then have "1 = b \<longrightarrow> FULLADDER 0 b c = (XOR b c, AND b c)"
    by force
  then show ?thesis
    by (metis (full_types) AND_0_b FULLADDER_00c XOR_0_0 XOR_0_1 bit.exhaust)
qed

lemma FULLADDER_a0c: "FULLADDER a 0 c = (XOR a c,AND a c)"
  by (metis (full_types) AND_0_1 AND_1_1 AND_a_0 FULLADDER_000 FULLADDER_001 FULLADDER_100 FULLADDER_101 XOR_0_0 XOR_0_1 XOR_1_0 XOR_1_1 bit_not_one_iff)

lemma FULLADDER_a00: "FULLADDER a 0 0 = (a,0)"
proof (cases a)
  case zero
  then show ?thesis by simp
next
  case one
  then show ?thesis by simp
qed

lemma FULLADDER_0b0: "FULLADDER 0 b 0 = (b,0)"
proof (cases b)
  case zero
  then show ?thesis by simp
next
  case one
  then show ?thesis by simp
qed

lemma FULLADDER_abc: "FULLADDER a b c = (XOR a (XOR b c),OR (AND a b) (AND c (XOR a b)))"
  by (smt (z3) AND_0_0 AND_1_0 AND_a_1 FULLADDER_000 FULLADDER_001 FULLADDER_010 FULLADDER_011 FULLADDER_100 FULLADDER_101 FULLADDER_110 FULLADDER_111 OR_0_b OR_1_0 XOR_0_0 XOR_0_1 XOR_1_0 XOR_1_1 bit_not_one_iff)

lemma FULLADDER_carry_criteria: "(s,1) = FULLADDER a b c \<longrightarrow> (a = 1 \<and> b = 1) \<or> (c = 1 \<and> a = 1 \<and> b = 0) \<or> (c = 1 \<and> a = 0 \<and> b = 1)"
proof -
  have "(s, 1) \<noteq> FULLADDER 1 0 0"
    by simp
  then show ?thesis
    by (smt (z3) FULLADDER_00c FULLADDER_0b0 Pair_inject bit_not_zero_iff)
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
text \<open>Since the book associated with Nand2Tetris uses Big Endian convention, I follow their
convention. Realistically, we should refactor this out, so as to force the user to import
their desired Endianess.\<close>

lemma "0xFF = 255" by (rule refl)

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

(*

abbreviation xF :: Hex where "xF \<equiv> Hex 1 1 1 1"
*)

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

lemma "XF = Hex 1 1 1 1" by auto


fun Hex_of_list :: "bit list \<Rightarrow> Hex" where
  "Hex_of_list [] = Hex 0 0 0 0" |
  "Hex_of_list [d] = Hex 0 0 0 d" |
  "Hex_of_list [c,d] = Hex 0 0 c d" |
  "Hex_of_list [b,c,d] = Hex 0 b c d" |
  "Hex_of_list [a,b,c,d] = Hex a b c d" |
  "Hex_of_list (a # xs) = Hex_of_list xs"

datatype Word = Word Hex Hex Hex Hex

consts to_list :: "'a \<Rightarrow> bit list"
overloading
  to_list_Hex \<equiv> "to_list :: Hex \<Rightarrow> bit list"
  to_list_Word \<equiv> "to_list :: Word \<Rightarrow> bit list"
begin
fun to_list_Hex where
  "to_list_Hex (Hex a b c d) = [a,b,c,d]"

fun to_list_Word where
  "to_list_Word (Word h1 h2 h3 h4) = (to_list h1) @ (to_list h2) @ (to_list h3) @ (to_list h4)"
end

fun Hex_to_nat :: "Hex \<Rightarrow> nat" where
  "Hex_to_nat (Hex a b c d) = (if 1=d then (1::nat) else 0) + (if 1=c then 2 else 0) +
    (if 1=b then 4 else 0) + (if 1=a then 8 else 0)"

fun Word_to_nat :: "Word \<Rightarrow> nat" where
  "Word_to_nat (Word h1 h2 h3 h4) = (Hex_to_nat h1) + 16*(Hex_to_nat h2) + 256*(Hex_to_nat h3) + 4096*(Hex_to_nat h4)"

fun nat_to_Hex :: "nat \<Rightarrow> Hex" where
"nat_to_Hex n = (let m = (n mod 16) in
 if m = 0 then (Hex 0 0 0 0)
 else if m = (1::nat) then (Hex 0 0 0 1)
 else if m = 2 then (Hex 0 0 1 0)
 else if m = 3 then (Hex 0 0 1 1)
 else if m = 4 then (Hex 0 1 0 0)
 else if m = 5 then (Hex 0 1 0 1)
 else if m = 6 then (Hex 0 1 1 0)
 else if m = 7 then (Hex 0 1 1 1)
 else if m = 8 then (Hex 1 0 0 0)
 else if m = 9 then (Hex 1 0 0 1)
 else if m = 10 then (Hex 1 0 1 0)
 else if m = 11 then (Hex 1 0 1 1)
 else if m = 12 then (Hex 1 1 0 0)
 else if m = 13 then (Hex 1 1 0 1)
 else if m = 14 then (Hex 1 1 1 0)
 else (Hex 1 1 1 1))"

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

theorem Hex_to_nat_to_Hex: "nat_to_Hex (Hex_to_nat a) = a"
proof (cases a)
  case (Hex x1 x2 x3 x4)
  then show ?thesis by simp
qed

fun nat_to_Word :: "nat \<Rightarrow> Word" where
"nat_to_Word n = Word (nat_to_Hex ((n div 4096) mod 16)) (nat_to_Hex ((n div 256) mod 16))
  (nat_to_Hex ((n div 16) mod 16)) (nat_to_Hex (n mod 16))"

lemma mod_of_prod: "(a * b) mod a = 0" for a b :: nat
  using Euclidean_Rings.euclidean_semiring_cancel_class.mod_mult_self1_is_0 by simp

lemma Hex_to_nat_mod16 [simp]: "(Hex_to_nat x) mod 16 = Hex_to_nat x"
proof (cases x)
  case (Hex x1 x2 x3 x4)
  thus ?thesis by simp
qed

lemma Hex_unsigned_max: "Hex_to_nat x < 16"
  by (metis Hex_to_nat_mod16 mod_less_divisor zero_less_numeral)

lemma Word_unsigned_max: "Word_to_nat w < 65536"
proof (cases w)
  case A1: (Word w1 w2 w3 w4)
  have A2: "Hex_to_nat w1 \<le> 15 \<and> Hex_to_nat w2 \<le> 15 \<and> Hex_to_nat w3 \<le> 15 \<and> Hex_to_nat w4 \<le> 15"
    using A1 Hex_unsigned_max
    by (metis eval_nat_numeral(2) less_Suc_eq_le semiring_norm(26) semiring_norm(27))
  moreover have "Word_to_nat w = (Hex_to_nat w1) + 16*(Hex_to_nat w2) + 256*(Hex_to_nat w3) + 4096*(Hex_to_nat w4)"
    by (simp add: A1)
  ultimately have A3: "Word_to_nat w < 16 + 16*15 + 256*15 + 4096*15"
    by auto
  then show ?thesis by simp
qed

lemma Word_to_nat_mod65536: "(Word_to_nat w) mod 65536 = Word_to_nat w"
  by (simp add: Word_unsigned_max)

fun split :: "nat \<Rightarrow> 'a list \<Rightarrow> ('a list) * ('a list)" where
  "split n xs = (take n xs, drop n xs)"

fun sign_bit :: "Word \<Rightarrow> bit" where
"sign_bit (Word (Hex s _ _ _) _ _ _) = s"

section \<open>Logic Gates for Hexadecimals\<close>

fun NOT_Hex :: \<open>Hex \<Rightarrow> Hex\<close>
  where \<open>NOT_Hex (Hex a b c d) = Hex (NOT a) (NOT b) (NOT c) (NOT d)\<close>

lemma NOT_NOT_Hex: "NOT_Hex (NOT_Hex a) = a"
proof (cases a)
  case (Hex x1 x2 x3 x4)
  then show ?thesis using NOT_NOT by auto
qed

fun AND_Hex :: \<open>Hex \<Rightarrow> Hex \<Rightarrow> Hex\<close> where
  "AND_Hex (Hex a1 b1 c1 d1) (Hex a2 b2 c2 d2) = Hex (AND a1 a2) (AND b1 b2) (AND c1 c2) (AND d1 d2)"

fun OR_Hex :: \<open>Hex \<Rightarrow> Hex \<Rightarrow> Hex\<close> where
  "OR_Hex (Hex a1 b1 c1 d1) (Hex a2 b2 c2 d2) = Hex (OR a1 a2) (OR b1 b2) (OR c1 c2) (OR d1 d2)"

fun XOR_Hex :: \<open>Hex \<Rightarrow> Hex \<Rightarrow> Hex\<close> where
  "XOR_Hex (Hex a1 b1 c1 d1) (Hex a2 b2 c2 d2) = Hex (XOR a1 a2) (XOR b1 b2) (XOR c1 c2) (XOR d1 d2)"

definition MUX_Hex :: \<open>Hex \<Rightarrow> Hex \<Rightarrow> bit \<Rightarrow> Hex\<close> where [simp]:
  "MUX_Hex a b s \<equiv> case a of (Hex a1 b1 c1 d1) \<Rightarrow> (case b of (Hex a2 b2 c2 d2) \<Rightarrow> Hex (MUX a1 a2 s) (MUX b1 b2 s) (MUX c1 c2 s) (MUX d1 d2 s))"

lemma MUX_Hex_left [simp]: "MUX_Hex a b 0 = a"
proof (cases a)
  case A1: (Hex a1 a2 a3 a4)
  then show ?thesis
  proof (cases b)
    case A2: (Hex b1 b2 b3 b4)
    then show ?thesis using A1 by simp
  qed
qed

lemma MUX_Hex_right [simp]: "MUX_Hex a b 1 = b"
proof (cases a)
  case A1: (Hex a1 a2 a3 a4)
  then show ?thesis
  proof (cases b)
    case A2: (Hex b1 b2 b3 b4)
    then show ?thesis using A1 by simp
  qed
qed

section \<open>Logic Gates for Words\<close>

fun OR8 :: \<open>Hex \<Rightarrow> Hex \<Rightarrow> bit\<close> where
  "OR8 (Hex a1 b1 c1 d1) (Hex a2 b2 c2 d2) = OR (OR a1 a2) (OR (OR b1 b2) (OR (OR c1 c2) (OR d1 d2)))"

lemma OR8_zero: "OR8 (0 :: Hex) (0 :: Hex) = 0"
  by (simp add: zero_Hex_def)

lemma OR8_zero_iff_zero: "OR a b = 0 \<longleftrightarrow> a = 0 \<and> b = 0"
  using NAND.elims by fastforce

fun ISZERO16 :: \<open>Word \<Rightarrow> bit\<close> where
  "ISZERO16 (Word a b c d) = NOT (OR (OR8 a b) (OR8 c d))"


lemma ISZERO16_check: "ISZERO16 (Word 0 0 0 0) = 1"
proof-
  have "ISZERO16 (Word 0 0 0 0) = NOT (OR (OR8 0 0) (OR8 0 0))" by simp
  moreover have "NOT (OR (OR8 0 0) (OR8 0 0)) = NOT (OR 0 0)" using OR8_zero by simp
  moreover have "NOT (OR 0 0) = 1" by simp
  thus ?thesis by (simp add: OR8_zero)
qed

lemma ISZERO16_zero: "ISZERO16 (Word a b c d) = 1 \<longleftrightarrow> a = 0 \<and> b = 0 \<and> c = 0 \<and> d = 0"
proof
  assume A1: "ISZERO16 (Word a b c d) = 1"
  then have "NOT (OR (OR8 a b) (OR8 c d)) = 1" by simp
  then have "OR (OR8 a b) (OR8 c d) = 0" using NAND.elims by auto
  then have A2: "(OR8 a b) = 0 \<and> (OR8 c d) = 0" by (metis OR_0_b OR_1_b bit_not_zero_iff)
  then show "a = 0 \<and> b = 0 \<and> c = 0 \<and> d = 0"
    by (metis (no_types, lifting) Hex.exhaust OR8.simps OR8_zero_iff_zero zero_Hex_def)
next
  assume A1: "a = 0 \<and> b = 0 \<and> c = 0 \<and> d = 0"
  then have "OR8 a b = 0 \<and> OR8 c d = 0" by (simp add: OR8_zero)
  then have "OR (OR8 a b) (OR8 c d) = 0" by simp
  then have "NOT (OR (OR8 a b) (OR8 c d)) = 1" by simp
  then show "ISZERO16 (Word a b c d) = 1" using A1 by auto
qed

fun NOT16 :: \<open>Word \<Rightarrow> Word\<close> where
  "NOT16 (Word a b c d) = Word (NOT_Hex a) (NOT_Hex b) (NOT_Hex c) (NOT_Hex d)"

lemma NOT16_NOT16: "NOT16 (NOT16 w) = w"
proof (cases w)
  case (Word w1 w2 w3 w4)
  then show ?thesis using NOT_NOT_Hex by auto
qed

fun AND16 :: \<open>Word \<Rightarrow> Word \<Rightarrow> Word\<close> where
  "AND16 (Word a1 a2 a3 a4) (Word b1 b2 b3 b4) = Word (AND_Hex a1 b1) (AND_Hex a2 b2) (AND_Hex a3 b3) (AND_Hex a4 b4)"

fun OR16 :: \<open>Word \<Rightarrow> Word \<Rightarrow> Word\<close> where
  "OR16 (Word a1 a2 a3 a4) (Word b1 b2 b3 b4) = Word (OR_Hex a1 b1) (OR_Hex a2 b2) (OR_Hex a3 b3) (OR_Hex a4 b4)"

fun MUX16 :: \<open>Word \<Rightarrow> Word \<Rightarrow> bit \<Rightarrow> Word\<close> where
  "MUX16 (Word a1 b1 c1 d1) (Word a2 b2 c2 d2) s = Word (MUX_Hex a1 a2 s) (MUX_Hex b1 b2 s) (MUX_Hex c1 c2 s) (MUX_Hex d1 d2 s)"

lemma MUX16_left [simp]: "MUX16 a b 0 = a"
proof (cases a)
  case A1: (Word a1 a2 a3 a4)
  then show ?thesis
  proof (cases b)
    case A2: (Word y1 y2 y3 y4)
    then show ?thesis using A1 MUX_Hex_left by auto
  qed
qed

lemma MUX16_right [simp]: "MUX16 a b 1 = b"
proof (cases a)
  case A1: (Word a1 a2 a3 a4)
  then show ?thesis
  proof (cases b)
    case A2: (Word y1 y2 y3 y4)
    then show ?thesis using A1 MUX_Hex_right by auto
  qed
qed

section \<open>Arithmetic Gates for Hex and Words\<close>
(* Chained FULLADDERs returning the sum and its carry bit. *)
fun ADDER_Hex :: \<open>Hex \<Rightarrow> Hex \<Rightarrow> bit \<Rightarrow> Hex * bit\<close> where
"ADDER_Hex (Hex a1 a2 a3 a4) (Hex b1 b2 b3 b4) c = (let (s4,c4) = FULLADDER a4 b4 c
in let (s3,c3) = FULLADDER a3 b3 c4
in let (s2,c2) = FULLADDER a2 b2 c3
in let (s1,c1) = FULLADDER a1 b1 c2
in (Hex s1 s2 s3 s4, c1))"

lemma ADDER_Hex_0b0: "ADDER_Hex (Hex 0 0 0 0) b 0 = (b, 0)"
proof (cases b)
  case A1: (Hex b1 b2 b3 b4)
  then show ?thesis using A1 FULLADDER_0b0 by auto
qed

lemma ADDER_Hex_a00: "ADDER_Hex a (Hex 0 0 0 0) 0 = (a, 0)"
proof (cases a)
  case A1: (Hex a1 a2 a3 a4)
  then show ?thesis using A1 FULLADDER_a00 by auto
qed

lemma ADDER_Hex_check: "Hex_to_nat (fst (ADDER_Hex a b 0)) = ((Hex_to_nat a) + (Hex_to_nat b)) mod 16"
proof (cases a)
  case A1: (Hex a1 a2 a3 a4)
  then show ?thesis
  proof (cases b)
    case A2: (Hex b1 b2 b3 b4)
    then show ?thesis using A1 by auto
  qed
qed

lemma ADDER_Hex_small: "(Hex_to_nat a) + (Hex_to_nat b) < 16 \<longrightarrow> (s,0 :: bit) = ADDER_Hex a b 0 \<longrightarrow> (Hex_to_nat a) + (Hex_to_nat b) = (Hex_to_nat s)"
proof -
  have "s = fst (s, 0::bit)"
    by auto
  then show ?thesis
    by (smt (z3) ADDER_Hex_check mod_less)
qed

lemma ADDER_Hex_check2: "(s,0 :: bit) = ADDER_Hex a b 0 \<longrightarrow> (Hex_to_nat a) + (Hex_to_nat b) = (Hex_to_nat s)"
proof (cases a)
  case A1: (Hex a1 a2 a3 a4)
  then show ?thesis
  proof (cases b)
    case (Hex x1 x2 x3 x4)
    then show ?thesis using A1 ADDER_Hex_check by simp
  qed
qed

lemma ADDER_Hex_cc_01: "(s,1) = ADDER_Hex (Hex 0 a2 a3 a4) (Hex 1 b2 b3 b4) c \<longrightarrow> 
(Hex_to_nat (Hex 1 b2 b3 b4)) + (Hex_to_nat (Hex 0 a2 a3 a4)) + (if (c=1) then 1 else 0) = 16 + Hex_to_nat s"
 by (simp add: FULLADDER_a00)

lemma ADDER_Hex_cc_10: "(s,1) = ADDER_Hex (Hex 1 a2 a3 a4) (Hex 0 b2 b3 b4) c \<longrightarrow>
(Hex_to_nat (Hex 0 b2 b3 b4)) + (Hex_to_nat (Hex 1 a2 a3 a4)) + (if (c=1) then 1 else 0) = 16 + Hex_to_nat s"
 by (simp add: FULLADDER_a00)

lemma ADDER_Hex_cc_11: "(s,1) = ADDER_Hex (Hex 1 a2 a3 a4) (Hex 1 b2 b3 b4) c \<longrightarrow>
(Hex_to_nat (Hex 1 b2 b3 b4)) + (Hex_to_nat (Hex 1 a2 a3 a4))+ (if (c=1) then 1 else 0) = 16 + Hex_to_nat s"
 by (simp add: FULLADDER_a00)

lemma ADDER_Hex_check3: "(s,1 :: bit) = ADDER_Hex a b 0 \<longrightarrow> (Hex_to_nat a) + (Hex_to_nat b) = 16 + (Hex_to_nat s)"
proof (cases a)
  case A: (Hex a1 a2 a3 a4)
  then show ?thesis
  proof (cases b)
    case (Hex b1 b2 b3 b4)
    then show ?thesis using A ADDER_Hex_cc_01 ADDER_Hex_cc_10 by simp
  qed
qed

theorem ADDER_Hex_checks: "(s,c :: bit) = ADDER_Hex a b 0 \<longrightarrow>
  (Hex_to_nat a) + (Hex_to_nat b) = (if (c=1) then 16 else 0) + (Hex_to_nat s)"
  by (simp add: ADDER_Hex_check2 ADDER_Hex_check3)

lemma ADDER_Hex_check_carry2: "(s,0 :: bit) = ADDER_Hex a b 1 \<longrightarrow> (Hex_to_nat a) + (Hex_to_nat b) + 1 = (Hex_to_nat s)"
proof (cases a)
  case A1: (Hex a1 a2 a3 a4)
  then show ?thesis
  proof (cases b)
    case (Hex x1 x2 x3 x4)
    then show ?thesis using A1 ADDER_Hex_check by simp
  qed
qed

lemma ADDER_Hex_check_carry3: "(s,1 :: bit) = ADDER_Hex a b 1 \<longrightarrow> (Hex_to_nat a) + (Hex_to_nat b) + 1 = 16 + (Hex_to_nat s)"
proof (cases a)
  case A: (Hex a1 a2 a3 a4)
  then show ?thesis
  proof (cases b)
    case (Hex b1 b2 b3 b4)
    then show ?thesis using A ADDER_Hex_cc_01 ADDER_Hex_cc_10 by simp
  qed
qed

theorem ADDER_Hex_check_carry: "(s, c :: bit) = ADDER_Hex a b 1 \<longrightarrow>
  (Hex_to_nat a) + (Hex_to_nat b) + 1 = (if (c=1) then 16 else 0) + (Hex_to_nat s)"
  using ADDER_Hex_check_carry2 ADDER_Hex_check_carry3 by auto

(* Add two words together, does not signal overflow or underflow, discards carry bit. *)
fun ADDER16 :: \<open>Word \<Rightarrow> Word \<Rightarrow> Word\<close> where
"ADDER16 (Word a1 a2 a3 a4) (Word b1 b2 b3 b4) = (let (s4,c4) = ADDER_Hex a4 b4 0
in let (s3,c3) = ADDER_Hex a3 b3 c4
in let (s2,c2) = ADDER_Hex a2 b2 c3
in let (s1,c1) = ADDER_Hex a1 b1 c2
in (Word s1 s2 s3 s4))"

lemma ADDER16_0b: "ADDER16 (Word 0 0 0 0) b = b"
proof (cases b)
  case B: (Word b1 b2 b3 b4)
  then show ?thesis by (simp add: ADDER_Hex_0b0 zero_Hex_def)
qed

lemma ADDER16_a0: "ADDER16 a (Word 0 0 0 0) = a"
proof (cases a)
  case (Word a1 a2 a3 a4)
  then show ?thesis by (simp add: ADDER_Hex_a00 zero_Hex_def)
qed

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
    then show ?thesis sorry
  qed
qed

fun INC16 :: \<open>Word \<Rightarrow> Word\<close> where
"INC16 a = ADDER16 a (Word 0 0 0 1)"

section \<open>Arithmetic Logical Unit\<close>

fun NEGATE16 :: \<open>Word \<Rightarrow> Word\<close> where
"NEGATE16 w = INC16 (NOT16 w)"

lemma INC16_ffff: "INC16 (Word XF XF XF XF) = (Word 0 0 0 0)"
  by (simp add: one_Hex_def zero_Hex_def)

lemma NEGATE16_zero: "NEGATE16 (Word 0 0 0 0) = (Word 0 0 0 0)"
  by (metis (mono_tags, lifting) INC16_ffff NEGATE16.elims NOT16.simps NOT_0 NOT_Hex.simps zero_Hex_def)

fun SUB16 :: \<open>Word \<Rightarrow> Word \<Rightarrow> Word\<close> where
"SUB16 x y = ADDER16 x (NEGATE16 y)"

fun DEC16 :: \<open>Word \<Rightarrow> Word\<close> where
"DEC16 x = SUB16 x (Word 0 0 0 1)"

lemma NOT16_zero: "NOT16 (Word 0 0 0 0) = Word XF XF XF XF"
  by (simp add: zero_Hex_def)

fun ZERO_OUT_WORD :: \<open>Word \<Rightarrow> bit \<Rightarrow> Word\<close> where
"ZERO_OUT_WORD w zr = MUX16 w (Word 0 0 0 0) zr"

lemma ZERO_OUT_WORD_isZero: "ISZERO16 (ZERO_OUT_WORD w 1) = 1"
  using ISZERO16_zero by auto

fun NEGATE_WORD :: \<open>Word \<Rightarrow> bit \<Rightarrow> Word\<close> where
"NEGATE_WORD w ng = MUX16 w (NEGATE16 w) ng"

fun ZERO_OR_NEGATE :: \<open>Word \<Rightarrow> bit \<Rightarrow> bit \<Rightarrow> Word\<close> where
"ZERO_OR_NEGATE w zr ng = (NEGATE_WORD (ZERO_OUT_WORD w zr) ng)"

lemma ZERO_OR_NEGATE_w01 [simp]: "ZERO_OR_NEGATE w 0 1 = NEGATE16 w" by simp

lemma ZERO_OR_NEGATE_w10 [simp]: "ZERO_OR_NEGATE w 1 0 = (Word 0 0 0 0)" by simp

fun ADDER16_OR_AND16 :: \<open>Word \<Rightarrow> Word \<Rightarrow> bit \<Rightarrow> Word\<close> where
"ADDER16_OR_AND16 a b f = MUX16 (AND16 a b) (ADDER16 a b) f"

lemma ADDER_OR_AND_ab1 [simp]: "ADDER16_OR_AND16 a b 1 = ADDER16 a b"
  by simp

lemma ADDER_OR_AND_ab0 [simp]: "ADDER16_OR_AND16 a b 0 = AND16 a b"
  by simp

(* The ALU operation without transforming the output. *)
fun ALU_op :: \<open>Word \<Rightarrow> Word \<Rightarrow> bit \<Rightarrow> bit \<Rightarrow> bit \<Rightarrow> bit \<Rightarrow> bit \<Rightarrow> Word\<close> where
"ALU_op x y zx nx zy ny f = (ADDER16_OR_AND16 (ZERO_OR_NEGATE x zx nx) (ZERO_OR_NEGATE y zy ny) f)"

fun ALU :: \<open>Word \<Rightarrow> Word \<Rightarrow> bit \<Rightarrow> bit \<Rightarrow> bit \<Rightarrow> bit \<Rightarrow> bit \<Rightarrow> bit \<Rightarrow> Word * bit * bit\<close> where
"ALU x y zx nx zy ny f no = (let sym = ALU_op x y zx nx zy ny f
in let output = MUX16 sym (NOT16 sym) no
in (output, ISZERO16 output, sign_bit output))"

text \<open>To prove correctness of the ALU implementation, we should check each of the 19 cases for the
possible outputs.\<close>
lemma ALU_101010: "ALU x y 1 0 1 0 1 0 = (Word 0 0 0 0, 1, 0)"
  by (simp add: zero_Hex_def)

lemma ALU_111111: "ALU x y 1 1 1 1 1 1 = (Word 0 0 0 1, 0, 0)"
  oops

lemma ALU_111010: "ALU x y 1 1 1 0 1 0 = (Word xF xF xF xF, 0, 1)" 
  oops

lemma ALU_001100: "ALU x y 0 0 1 1 0 0 = (x, ISZERO16 x, sign_bit x)" sledgehammer (add: ADDER16_a0 ISZERO16_zero)
  oops

lemma ALU_110000: "ALU x y 1 1 0 0 0 0 = (y, ISZERO16 y, sign_bit y)"
  oops

lemma ALU_001101: "ALU x y 0 0 1 1 0 1 = (NOT16 x, ISZERO16 (NOT16 x), sign_bit (NOT16 x))"
  oops

lemma ALU_110001: "ALU x y 1 1 0 0 0 1 = (NOT16 y, ISZERO16 (NOT16 y), sign_bit (NOT16 y))"
  oops

lemma ALU_001111: "ALU x y 0 0 1 1 1 1 = (NEGATE16 x, ISZERO16 (NEGATE16 x), sign_bit (NEGATE16 x))"
  oops

lemma ALU_110011: "ALU x y 1 1 0 0 1 1 = (NEGATE16 y, ISZERO16 (NEGATE16 y), sign_bit (NEGATE16 y))"
  oops

lemma ALU_011111: "ALU x y 0 1 1 1 1 1 = (INC16 x, ISZERO16 (INC16 x), sign_bit (INC16 x))"
  oops

lemma ALU_110111: "ALU x y 1 1 0 1 1 1 = (INC16 y, ISZERO16 (INC16 y), sign_bit (INC16 y))"
  oops

lemma ALU_001110: "ALU x y 0 0 1 1 1 0 = (DEC16 x, ISZERO16 (DEC16 x), sign_bit (DEC16 x))"
  oops

lemma ALU_110010: "ALU x y 1 1 0 0 1 0 = (DEC16 y, ISZERO16 (DEC16 y), sign_bit (DEC16 y))"
  oops

lemma ALU_000010: "ALU x y 0 0 0 0 1 0 = (ADDER16 x y, ISZERO16 (ADDER16 x y), sign_bit (ADDER16 x y))"
  by (smt (z3) ADDER_OR_AND_ab1 ALU.simps ALU_op.simps MUX16_left NEGATE_WORD.simps ZERO_OR_NEGATE.simps ZERO_OUT_WORD.simps)
(* by (metis ADDER_OR_AND_ab1 ALU.simps ALU_op.simps MUX16_left NEGATE_WORD.simps ZERO_OR_NEGATE.simps ZERO_OUT_WORD.simps) *)

lemma ALU_010011: "ALU x y 0 1 0 0 1 1 = (SUB16 x y, ISZERO16 (SUB16 x y), sign_bit (SUB16 x y))"
  oops

lemma ALU_000111: "ALU x y 0 0 0 1 1 1 = (SUB16 y x, ISZERO16 (SUB16 y x), sign_bit (SUB16 y x))"
  oops

lemma ALU_000000: "ALU x y 0 0 0 0 0 0 = (AND16 x y, ISZERO16 (AND16 x y), sign_bit (AND16 x y))"
  by (metis ADDER_OR_AND_ab0 ALU.simps ALU_op.simps MUX16_left NEGATE_WORD.simps ZERO_OR_NEGATE.simps ZERO_OUT_WORD.simps)

lemma ALU_010101: "ALU x y 0 1 0 1 0 1 = (OR16 x y, ISZERO16 (OR16 x y), sign_bit (OR16 x y))"
  oops

end