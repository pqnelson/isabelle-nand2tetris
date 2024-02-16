theory Scratch
  imports Main "~~/src/HOL/Library/Z2"
begin

fun NAND :: \<open>bit \<Rightarrow> bit \<Rightarrow> bit\<close> where
\<open>NAND (1::bit) (1::bit) = (0::bit)\<close> |
\<open>NAND (1::bit) (0::bit) = (1::bit)\<close> |
\<open>NAND (0::bit) (1::bit) = (1::bit)\<close> |
\<open>NAND (0::bit) (0::bit) = (1::bit)\<close>

definition NOT :: \<open>bit \<Rightarrow> bit\<close>
  where [simp]: \<open>NOT a \<equiv> (NAND a a)\<close>

lemma NOT_0: "NOT (0::bit) \<equiv> (1::bit)"
  apply simp
  done

lemma NOT_1: "NOT (1::bit) \<equiv> (0::bit)"
  apply simp
  done

definition AND :: \<open>bit \<Rightarrow> bit \<Rightarrow> bit\<close>
  where [simp]: \<open>AND a b \<equiv> NAND (NAND a b) (NAND a b)\<close>

lemma AND_0_0: "AND (0::bit) (0::bit) \<equiv> (0::bit)"
  apply simp
  done

lemma AND_0_1: "AND (0::bit) (1::bit) \<equiv> (0::bit)"
  apply simp
  done

lemma AND_1_0: "AND (1::bit) (0::bit) \<equiv> (0::bit)"
  apply simp
  done

lemma AND_1_1: "AND (1::bit) (1::bit) \<equiv> (1::bit)"
  apply simp
  done

definition OR :: \<open>bit \<Rightarrow> bit \<Rightarrow> bit\<close>
  where [simp]: \<open>OR a b \<equiv> NAND (NOT a) (NOT b)\<close>

lemma OR_0_0: "OR (0::bit) (0::bit) \<equiv> (0::bit)"
  apply simp
  done

lemma OR_0_1: "OR (0::bit) (1::bit) \<equiv> (1::bit)"
  apply simp
  done

lemma OR_1_0: "OR (1::bit) (0::bit) \<equiv> (1::bit)"
  apply simp
  done

lemma OR_1_1: "OR (1::bit) (1::bit) \<equiv> (1::bit)"
  apply simp
  done

end