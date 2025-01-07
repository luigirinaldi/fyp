theory test imports Main begin

lemma rw_mod_sum_1:
  "((p > 0) \<and> (q > 0) \<and> (p \<ge> q)) \<Longrightarrow> 
  (((a::int) mod 2^p) + (b::int)) mod 2^q = (a + b) mod 2^q"
  by (metis dvd_power_le even_numeral mod_add_cong mod_mod_cancel)

lemma rw_mod_diff_1:
  "((p > 0) \<and> (q > 0) \<and> (p \<ge> q)) \<Longrightarrow> 
  (((a::int) mod 2^p) - (b::int)) mod 2^q = (a - b) mod 2^q"
  by (metis add_uminus_conv_diff rw_mod_sum_1)

lemma rw_mod_sum_2:  
  assumes"(p > 0) \<and> (q > 0) \<and> (r > 0) \<and> (p < q) \<and> (r < q)" 
  shows "(((a::int) mod 2^p) + (b::int) mod 2^r) mod 2^q = (a mod 2^p + b mod 2^r)" 
  proof -
  have "(a mod 2^p) \<le> 2^p - 1" by simp
  also have "... \<le> 2^(q - 1) - 1" using assms diff_le_mono by (simp add: add_le_imp_le_diff less_iff_succ_less_eq)
  moreover have "(b mod 2^r) \<le> 2^r - 1" by auto
  then have "... \<le> 2^(q -1) - 1" using assms diff_le_mono by (simp add: add_le_imp_le_diff less_iff_succ_less_eq)
  ultimately have "((a mod 2^p) + (b mod 2^r)) \<le> 2*(2^(q - 1) - 1)" 
  using \<open>a mod 2 ^ p \<le> 2 ^ p - 1\<close> \<open>b mod 2 ^ r \<le> 2 ^ r - 1\<close> by (smt (verit, ccfv_SIG))
  moreover have "2*((2::nat)^(q - 1) - 1) < 2^q" using assms by (metis diff_less diff_mult_distrib2 neq0_conv numeral_Bit0_eq_double numerals(1) power_eq_0_iff power_eq_if zero_power2) 
  ultimately show ?thesis by (smt (verit, best) One_nat_def Suc_pred assms mod_pos_pos_trivial pos_mod_sign push_bit_Suc push_bit_double push_bit_minus_one zero_less_power)
qed


definition "assoc_rhs (a::int) (t::nat) (b::int) (s::nat) (c::int) (p::nat) (q::nat) (r::nat)
    = ((a mod 2^t) + (((b mod 2^s) + (c mod 2^p)) mod 2^q)) mod 2^r"

definition "assoc_lhs (a::int) (t::nat) (b::int) (s::nat) (c::int) (p::nat) (q::nat) (r::nat)
    = ((((a mod 2^t) + (b mod 2^s)) mod 2^q) + (c mod 2^p)) mod 2^r"
 
theorem assoc_equiv:
" ((a mod 2^t) + (((b mod 2^s) + (c mod 2^p)) mod 2^q)) mod 2^r
= ((((a mod 2^t) + (b mod 2^s)) mod 2^q) + (c mod 2^p)) mod 2^r"
if "(r > 0) \<and> (p > 0) \<and> (q > 0) \<and> (s > 0)"
and case_1: "(p < q \<and> s < q \<and> t < q) \<or> (q \<ge> r)"
for a b c :: int and p q r s t :: nat
by (smt (verit, del_insts) rw_mod_sum_1 rw_mod_sum_2 assoc_lhs_def assoc_rhs_def add.commute 
    case_1 less_zeroE linorder_neqE_nat mod_pos_pos_trivial pos_mod_bound pos_mod_sign 
    power_le_one_iff that(1) zero_less_power)

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
     sorry
     (*
by (simp add: rw_mod_sum_2 mod_prod assms(1) assms(2) assms(3) distrib_left less_or_eq_imp_le)*)


lemma mul_remove_mod:
assumes "p > 0 \<and> q > 0"
assumes "p \<ge> q"
shows "(((a::nat) mod 2^p) * (b::nat)) mod 2^q = (((a::nat) * (b::nat)) mod 2^q)"
by (metis assms(2) dvd_power_le gcd_nat.refl mod_mod_cancel mod_mult_cong)

theorem mod_mul_distrib_2:
assumes "p > 0 \<and> s > 0 \<and> t > 0 \<and> q > 0 \<and> r > 0 \<and> u > 0 \<and> v > 0"
assumes "a \<in> \<nat> \<and> b  \<in> \<nat>  \<and> c \<in> \<nat> \<and> p \<in> \<nat> \<and> q \<in> \<nat> \<and> r \<in> \<nat> \<and> s \<in> \<nat> \<and> t \<in> \<nat> \<and> u \<in> \<nat> \<and> v \<in> \<nat>"
assumes "u \<ge> r \<and> v \<ge> r \<and> q \<ge> r"
shows "((((a::nat) mod 2^p) * (((b mod 2^s) + (c mod 2^t)) mod 2^q) mod 2^r)
     = ((((a mod 2^p) * (b mod 2^s)) mod 2^u) + ((a mod 2^p) * (c mod 2^t)) mod 2^v) mod 2^r)"
     by (smt (verit, ccfv_threshold) 
       assms mul_remove_mod rw_mod_sum_1 
       distrib_left le_imp_power_dvd mod_add_cong mod_mod_cancel mult.commute)

     lemma
     "2*(k mod 2^(q-1)) - (k mod 2^q) = ((2 * k) mod (2 * 2^(q-1))) - (k mod 2^q)"
     for k :: int and q :: nat
     by simp

     definition "signed (a::int) (p::nat) = 2*(a mod 2^(p-1)) - (a mod 2^p)"

     value "signed 21 3"
     value "signed 8 5"
     
  lemma 
     (*"((a mod 2^p) + (2*(((b mod 2^p) + (c mod 2^p)) mod 2^(q-1)) - (((b mod 2^p) + (c mod 2^p)) mod 2^q))) mod 2^r
     =((2*(((a mod 2^p) + (b mod 2^p)) mod 2^(q-1)) - (((a mod 2^p) + (b mod 2^p)) mod 2^q)) + (c mod 2^p)) mod 2^r"*)
     "((signed a p) + (signed ((signed b p) + (signed c p)) q)) mod 2^r
     =((signed ((signed a p) + (signed b p)) q) + (signed c p)) mod 2^r"
     
     if "p < q" and "q < r" for a b c :: int and p q r :: nat
     proof - 
     show ?thesis using signed_def that 