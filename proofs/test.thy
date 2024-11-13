theory test imports Main begin


definition "assoc_rhs (a::nat) (t::nat) (b::nat) (s::nat) (c::nat) (p::nat) (q::nat) (r::nat)
   = ((a mod 2^t) + (((b mod 2^s) + (c mod 2^p)) mod 2^q)) mod 2^r"

definition "assoc_lhs (a::nat) (t::nat) (b::nat) (s::nat) (c::nat) (p::nat) (q::nat) (r::nat)
 = ((((a mod 2^t) + (b mod 2^s)) mod 2^q) + (c mod 2^p)) mod 2^r"


 lemma "A \<and> B \<longrightarrow> B \<and> A"
 proof
 assume "A \<and> B"
 show "B \<and> A"
 proof 
 show B by (rule conjunct2 ) fact
 show A by (rule conjunct1 ) fact
 qed
 qed


 value "(2::nat)^2 > 2^(1 + 1) - 2"
 
 lemma simple_rewrite:
  "((p > 0) \<and> (q > 0) \<and> (p \<ge> q)) \<Longrightarrow> 
  (((a::nat) mod 2^p) + (b::nat)) mod 2^q = (a + b) mod 2^q"
  by (metis dvd_power_le even_numeral mod_add_cong mod_mod_cancel)

lemma simple_rewrite_2:  
  assumes"(p > 0) \<and> (q > 0) \<and> (p < q)" 
  shows "(((a::nat) mod 2^p) + (b::nat) mod 2^p) mod 2^q = ((a mod 2^p) + b mod 2^p)" 
  proof -
  have "(a mod 2^p) \<le> 2^p - 1" by (metis Suc_mask_eq_exp mask_nat_def mod_Suc_le_divisor) 
  also have "(b mod 2^p) \<le> 2^p - 1" by (metis Suc_mask_eq_exp mask_nat_def mod_Suc_le_divisor) 
  ultimately have mod_expr: "((a mod 2^p) + (b mod 2^p)) \<le> 2*(2^p - 1)" by simp
  have "(2::nat)^p  < 2^q" using assms by auto
  then have "(2::nat)^(p+1) - 1  < 2^q" by (metis One_nat_def Suc_pred add.right_neutral add_Suc_right not_less_eq one_less_numeral_iff power_strict_increasing_iff semiring_norm(76) zero_less_numeral zero_less_power)
  then have "(2::nat)^(p+1) - 2  < 2^q" by auto
  hence " 2*((2::nat)^p - 1) < 2^q" by auto
  hence "((a mod 2^p) + (b mod 2^p)) < 2^q" using mod_expr by auto
  hence "((a mod 2^p) + (b mod 2^p)) mod 2^q = ((a mod 2^p) + b mod 2^p)" by auto
  then show ?thesis by blast
  qed
  

 
theorem arbitrary_assoc:
assumes "(r > 0) \<and> (p > 0) \<and> (q > 0)  
  \<and> (
  (p < q) \<or> (q \<ge> r)
)
 "
 shows " 
      assoc_rhs a p b p c p q r 
        = assoc_lhs a p b p c p q r "
proof -
show ?thesis using simple_rewrite_2 simple_rewrite 
by (smt (z3) add.commute assms assoc_lhs_def assoc_rhs_def group_cancel.add1)