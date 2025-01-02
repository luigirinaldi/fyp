theory test imports Main begin

lemma rw_mod_sum_1:
  "((p > 0) \<and> (q > 0) \<and> (p \<ge> q)) \<Longrightarrow> 
  (((a::int) mod 2^p) + (b::int)) mod 2^q = (a + b) mod 2^q"
  by (metis dvd_power_le even_numeral mod_add_cong mod_mod_cancel)

lemma rw_mod_sum_2:  
  assumes"(p > 0) \<and> (q > 0) \<and> (r > 0) \<and> (p < q) \<and> (r < q)" 
  shows "(((a::nat) mod 2^p) + (b::nat) mod 2^r) mod 2^q = (a mod 2^p + b mod 2^r)" 
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
  


definition "assoc_rhs (a::nat) (t::nat) (b::nat) (s::nat) (c::nat) (p::nat) (q::nat) (r::nat)
    = ((a mod 2^t) + (((b mod 2^s) + (c mod 2^p)) mod 2^q)) mod 2^r"

definition "assoc_lhs (a::nat) (t::nat) (b::nat) (s::nat) (c::nat) (p::nat) (q::nat) (r::nat)
    = ((((a mod 2^t) + (b mod 2^s)) mod 2^q) + (c mod 2^p)) mod 2^r"
 
theorem assoc_equiv:
assumes "(r > 0) \<and> (p > 0) \<and> (q > 0) \<and> (s > 0) 
  \<and> (
  (p < q \<and> s < q) \<or> (q \<ge> r)
)
 "
 shows "  assoc_rhs a p b s c p q r 
        = assoc_lhs a p b s c p q r "
proof -
show ?thesis using rw_mod_sum_1 rw_mod_sum_2 
by (smt (z3) assms assoc_lhs_def assoc_rhs_def group_cancel.add1 le_imp_power_dvd mod_add_cong mod_mod_cancel)
qed

lemma distrib_power:
assumes "p > 0 \<and> q > 0"
assumes "p \<in> \<nat> \<and> q \<in> \<nat>"
shows "(((2::nat)^q) - 1) * ((2^p) - 1) = (2 ^ (p + q)) - (2^p) - (2^q) + 1"
proof -
have "(((2::nat)^q) - 1) * ((2^p) - 1) = (((2::nat)^q) - 1) * (2^p)  - 1 *  (((2::nat)^q) - 1)" by (simp add: diff_mult_distrib mult.commute)
also have "... =  (2^q)  * (2^p) - 1 * (2^p) - 1 *  ((2^q) - 1)" using diff_mult_distrib by presburger
also have "... =  (2^q)  * (2^p) - 1 * (2^p) - (2^q) + 1" using assms calculation 
by (smt (verit, best) Nat.add_diff_assoc2 Nat.diff_diff_right lambda_one 
    le_add1 le_add_diff_inverse linordered_semidom_class.add_diff_inverse 
    mult_pos_pos not_less_eq one_le_numeral one_le_power one_less_numeral_iff 
    one_less_power plus_1_eq_Suc semiring_norm(76) zero_less_diff)
then show ?thesis by (metis add.commute calculation mult_1 power_add)
qed 

lemma mod_prod:
assumes "p > 0 \<and> q > 0 \<and> r > 0"
assumes "p \<in> \<nat> \<and> q \<in> \<nat> \<and> r \<in> \<nat>"
assumes "r \<ge> (p + q)"
shows "(((a::nat) mod 2^p) * ((b::nat) mod 2^q)) mod 2^r = (((a::nat) mod 2^p) * ((b::nat) mod 2^q))"
proof - 
have "(a mod 2^p) \<le> 2^p - 1" by (metis Suc_mask_eq_exp mask_nat_def mod_Suc_le_divisor) 
moreover have "(b mod 2^q) \<le> 2^q - 1" by (metis Suc_mask_eq_exp mask_nat_def mod_Suc_le_divisor)
moreover have "(b mod 2^q) * (a mod 2^p)  \<le> (2^q - 1) * (2^p - 1)" using calculation(1) calculation(2) mult_le_mono by presburger
moreover have " ((2^q) - 1) * ((2^p) - 1) = ((2::nat) ^ (p + q)) - (2^p) - (2^q) + 1" using distrib_power assms(1) assms(2) by presburger
moreover have "((2::nat) ^ (p + q)) - (2^p) - (2^q) + 1 < ((2::nat) ^ (p + q))" using calculation(4) even_power mult.commute order.strict_iff_order by fastforce
moreover have "... \<le> 2^r" using assms(3) by auto
moreover have "(b mod 2^q) * (a mod 2^p) < 2^r" using calculation(3) calculation(4) calculation(5) calculation(6) by linarith
ultimately show ?thesis by (metis mod_less mult.commute)
qed

theorem mod_mul_distrib:
assumes "p > 0 \<and> s > 0 \<and> t > 0 \<and> q > 0 \<and> r > 0 \<and> u > 0 \<and> v > 0"
assumes "a \<in> \<nat> \<and> b  \<in> \<nat>  \<and> c \<in> \<nat> \<and> p \<in> \<nat> \<and> q \<in> \<nat> \<and> r \<in> \<nat> \<and> s \<in> \<nat> \<and> t \<in> \<nat> \<and> u \<in> \<nat> \<and> v \<in> \<nat>"
assumes "q > s \<and> q > t \<and> r > (q + a) \<and> u > (p + s) \<and> v > (p + t)"
shows "(((a mod 2^p) * (((b mod 2^s) + (c mod 2^t)) mod 2^q) mod 2^r)
     = ((((a mod 2^p) * (b mod 2^s)) mod 2^u) + ((a mod 2^p) * (c mod 2^t)) mod 2^v) mod 2^r)"
by (simp add: rw_mod_sum_2 mod_prod assms(1) assms(2) assms(3) distrib_left less_or_eq_imp_le)

