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
proof (cases a)
  assume A1: "a = 0"
  hence "NAND 0 0 = 1" by simp
  hence "NAND a 0 = 1" using A1 by simp
  thus ?thesis by simp
next
  assume A2: "a = 1"
  hence "NAND 1 0 = 1" by simp
  hence "NAND a 0 = 1" using A2 by simp
  thus ?thesis by simp
qed

lemma NAND_0_b [simp]: "NAND 0 b = 1"
proof (cases b)
  assume A1: "b = 0"
  hence "NAND 0 0 = 1" by simp
  hence "NAND 0 b = 1" using A1 by simp
  thus ?thesis by simp
next
  assume A2: "b = 1"
  hence "NAND 0 1 = 1" by simp
  hence "NAND 0 b = 1" using A2 by simp
  thus ?thesis by simp
qed

theorem NAND_comm: "NAND a b = NAND b a"
proof (cases b)
  assume "b = 0"
  thus ?thesis using NAND_a_0 NAND_0_b by auto
next
  assume A1: "b = 1"
  have "NAND a 1 = NAND 1 a"
  proof (cases a)
    assume A2: "a = 0"
    thus ?thesis using A1 NAND_a_0 NAND_0_b by auto
  next
    assume "a = 1"
    thus ?thesis by simp
  qed
  thus ?thesis using A1 by simp
qed

definition NOT :: \<open>bit \<Rightarrow> bit\<close>
  where [simp]: \<open>NOT a \<equiv> (NAND a a)\<close>

lemma NOT_0 [simp]: "NOT (0::bit) \<equiv> (1::bit)"
  apply simp
  done

lemma NOT_1 [simp]: "NOT (1::bit) \<equiv> (0::bit)"
  apply simp
  done

theorem NOT_NOT: "NOT (NOT a) = a"
proof (cases a)
  assume A1: "a = 0"
  hence "NOT a = 1" by simp
  thus ?thesis using A1 by simp
next
  assume A2: "a = 1"
  hence "NOT a = 0" by simp
  thus ?thesis using A2 by simp
qed

definition AND :: \<open>bit \<Rightarrow> bit \<Rightarrow> bit\<close>
  where [simp]: \<open>AND a b \<equiv> NAND (NAND a b) (NAND a b)\<close>

lemma AND_0_0 [simp]: "AND (0::bit) (0::bit) \<equiv> (0::bit)"
  apply simp
  done

lemma AND_0_1 [simp]: "AND (0::bit) (1::bit) \<equiv> (0::bit)"
  apply simp
  done

lemma AND_1_0 [simp]: "AND (1::bit) (0::bit) \<equiv> (0::bit)"
  apply simp
  done

lemma AND_1_1 [simp]: "AND (1::bit) (1::bit) \<equiv> (1::bit)"
  apply simp
  done

lemma AND_a_1: "AND a 1 = a"
proof (cases a)
  assume "a = 0"
  thus ?thesis by simp
next
  assume "a = 1"
  thus ?thesis by simp
qed

lemma AND_a_0: "AND a 0 = 0"
proof (cases a)
  assume "a = 0"
  thus ?thesis by simp
next
  assume "a = 1"
  thus ?thesis by simp
qed

lemma AND_1_b: "AND 1 b = b"
proof (cases b)
  assume "b = 0"
  thus ?thesis by simp
next
  assume "b = 1"
  thus ?thesis by simp
qed

lemma AND_0_b: "AND 0 b = 0"
proof (cases b)
  assume "b = 0"
  thus ?thesis by simp
next
  assume "b = 1"
  thus ?thesis by simp
qed

theorem AND_comm: "AND a b = AND b a"
proof (cases b)
  assume "b = 0"
  thus ?thesis using AND_0_b AND_a_0 by simp
next
  assume "b = 1"
  thus ?thesis using AND_1_b AND_a_1 by simp
qed

\<comment>\<open>We can prove that NAND really is just "NOT AND"!\<close>
lemma NOT_AND_is_NAND: "NOT (AND a b) = NAND a b"
proof (cases a)
  assume "a = 0"
  thus ?thesis by simp
next
  assume A1: "a = 1"
  show ?thesis
  proof (cases b)
    assume "b = 0"
    thus ?thesis using A1 by simp
  next
    assume "b = 1"
    thus ?thesis using A1 by simp
  qed
qed

definition OR :: \<open>bit \<Rightarrow> bit \<Rightarrow> bit\<close>
  where [simp]: \<open>OR a b \<equiv> NAND (NOT a) (NOT b)\<close>

lemma OR_0_0 [simp]: "OR (0::bit) (0::bit) \<equiv> (0::bit)"
  apply simp
  done

lemma OR_0_1 [simp]: "OR (0::bit) (1::bit) \<equiv> (1::bit)"
  apply simp
  done

lemma OR_1_0 [simp]: "OR (1::bit) (0::bit) \<equiv> (1::bit)"
  apply simp
  done

lemma OR_1_1 [simp]: "OR (1::bit) (1::bit) \<equiv> (1::bit)"
  apply simp
  done

lemma OR_a_0 [simp]: "OR a 0 = a"
proof (cases a)
  assume "a = 0"
  thus ?thesis by simp
next
  assume "a = 1"
  thus ?thesis by simp
qed

lemma OR_0_b [simp]: "OR 0 b = b"
proof (cases b)
  assume "b = 0"
  thus ?thesis by simp
next
  assume "b = 1"
  thus ?thesis by simp
qed

lemma OR_a_1 [simp]: "OR a 1 = 1"
  apply simp
  done

lemma OR_1_b [simp]: "OR 1 b = 1"
  apply simp
  done

theorem OR_comm: "OR a b = OR b a"
proof-
  show ?thesis using NAND_comm by simp
qed

theorem de_Morgan_gate1: "NOT (AND a b) = OR (NOT a) (NOT b)"
proof (cases a)
  assume A1: "a = 0"
  thus ?thesis using AND_0_b by simp
next
  assume "a = 1"
  thus ?thesis using AND_1_b OR_0_b by simp
qed

theorem de_Morgan_gate2: "NOT (OR a b) = AND (NOT a) (NOT b)"
proof (cases a)
  assume "a = 0"
  thus ?thesis by simp
next
  assume "a = 1"
  thus ?thesis by simp
qed

definition MUX :: \<open>bit \<Rightarrow> bit \<Rightarrow> bit \<Rightarrow> bit\<close>
  where [simp]: \<open>MUX a b s \<equiv> NAND (NAND a (NOT s)) (NAND b s)\<close>

theorem MUX_left [simp]: "MUX a b 0 = a"
proof (cases a)
  assume "a = 0"
  thus ?thesis by simp
next
  assume "a = 1"
  thus ?thesis by simp
qed

theorem MUX_right [simp]: "MUX a b 1 = b"
proof (cases b)
  assume "b = 0"
  thus ?thesis by simp
next
  assume "b = 1"
  thus ?thesis using NAND_a_0 NAND_0_b by simp
qed

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