theory Scratch
  imports Main "~~/src/HOL/Library/Z2"
begin

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

end