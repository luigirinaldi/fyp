theory test imports Main begin


definition "assoc_rhs (a::nat) (t::nat) (b::nat) (s::nat) (c::nat) (p::nat) (q::nat) (r::nat)
   = ((a mod 2^t) + (((b mod 2^s) + (c mod 2^p)) mod 2^q)) mod 2^r"

definition "assoc_lhs (a::nat) (t::nat) (b::nat) (s::nat) (c::nat) (p::nat) (q::nat) (r::nat)
 = ((((a mod 2^t) + (b mod 2^s)) mod 2^q) + (c mod 2^p)) mod 2^r"

lemma rw_mod_sum_1:
  "((p > 0) \<and> (q > 0) \<and> (p \<ge> q)) \<Longrightarrow> 
  (((a::int) mod 2^p) + (b::int)) mod 2^q = (a + b) mod 2^q"
  by (metis dvd_power_le even_numeral mod_add_cong mod_mod_cancel)

lemma rw_mod_sum_2:  
  assumes"(p > 0) \<and> (q > 0) \<and> (r > 0) \<and> (p < q) \<and> (r < q)" 
  shows "(((a::nat) mod 2^p) + (b::nat) mod 2^r) mod 2^q = ((a mod 2^p) + b mod 2^r)" 
  proof -
  have "(a mod 2^p) \<le> 2^p - 1" by (metis Suc_mask_eq_exp mask_nat_def mod_Suc_le_divisor) 
  also have "... \<le> 2^(q - 1) - 1" using assms diff_le_mono by force
  moreover have "(b mod 2^r) \<le> 2^r - 1" by (metis Suc_mask_eq_exp mask_nat_def mod_Suc_le_divisor)
  then have "... \<le> 2^(q -1) - 1" using assms diff_le_mono by force
  ultimately have "((a mod 2^p) + (b mod 2^r)) \<le> 2*(2^(q - 1) - 1)" 
  using \<open>a mod 2 ^ p \<le> 2 ^ p - 1\<close> \<open>b mod 2 ^ r \<le> 2 ^ r - 1\<close> by linarith
  moreover have "2*((2::nat)^(q - 1) - 1) < 2^q" using assms by (metis diff_less diff_mult_distrib2 neq0_conv numeral_Bit0_eq_double numerals(1) power_eq_0_iff power_eq_if zero_power2) 
  ultimately have "((a mod 2^p) + (b mod 2^r)) mod 2^q = ((a mod 2^p) + b mod 2^r)" by simp
  then show ?thesis by blast
  qed
  

 
theorem arbitrary_assoc:
assumes "(r > 0) \<and> (p > 0) \<and> (q > 0) \<and> (s > 0) 
  \<and> (
  (p < q \<and> s < q) \<or> (q \<ge> r)
)
 "
 shows " 
      assoc_rhs a p b s c p q r 
        = assoc_lhs a p b s c p q r "
proof -
show ?thesis using rw_mod_sum_1 rw_mod_sum_2 
by (smt (z3) assms assoc_lhs_def assoc_rhs_def group_cancel.add1 le_imp_power_dvd mod_add_cong mod_mod_cancel)