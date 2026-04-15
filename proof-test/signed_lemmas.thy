theory signed_lemmas
  imports rewrite_defs arith_lemmas
begin
  
lemma redundant_signed: 
fixes a :: int 
fixes p :: nat
shows "bw p (signed p (bw p a)) = bw p a" (is "?lhs = ?rhs")
proof -
  have "?lhs =  (2 * (a mod 2 ^ p mod 2 ^ (p - 1)) mod 2 ^ p - a mod 2 ^ p mod 2 ^ p) mod 2 ^ p" apply (simp only: signed_def bw_def) done
  moreover have "... = ((2 * (a mod 2 ^ p) mod (2 * 2 ^ (p - 1))) mod 2 ^ p - a mod 2 ^ p mod 2 ^ p) mod 2 ^ p" using mult_mod_left by auto
  moreover have "... = ((2 * (a mod 2 ^ p) mod (2 ^ p)) mod 2 ^ p - a mod 2 ^ p mod 2 ^ p) mod 2 ^ p" using power_eq_if by (metis (no_types, lifting) mod_by_1)
  moreover have "... = (2*a - a) mod 2^p" by (simp add: mod_diff_left_eq mod_diff_right_eq mod_mult_right_eq) 
  ultimately show ?thesis by (metis bw_def eq_diff_eq mult_2)
qed

lemma signed_zext: 
  fixes a :: int
  fixes p :: nat
  assumes "q > p"
  shows "signed q (bw q (bw p a)) = bw p a" (is "?lhs = ?rhs")
proof -
  have "?lhs = bw q (2 * (bw (q - 1) (bw q (bw p a)))) - bw q (bw q (bw p a))" apply (simp only: signed_def) done
  moreover have "... = bw q (2 * bw p a) - bw q (bw p a)" using power_eq_if mod_by_1 mult_mod_left using assms reduce_mod by fastforce 
  ultimately show ?thesis by (metis add_diff_cancel_left' add_full_prec arith_lemmas.mult_2 assms less_le_not_le reduce_mod) 
qed

lemma prop_two: "(2 * (bw (p - 1) a)) = (bw p (2*a))" apply (simp only: bw_def) using mult_mod_left by (simp add: power_eq_if[of "2" p])

lemma bw_subset: 
  fixes p :: nat
  fixes a x y :: int
  assumes "a \<in> {x..y}"
  assumes "{x..y} \<subseteq> {0..2^p -1}"
  shows "bw p a = a"
proof -
  have "a \<le> 2^p -1" using assms by force
  moreover have "a \<ge> 0" using assms by simp
  ultimately show ?thesis using bw_def by simp
qed

lemma signed_of_neg: 
  fixes a :: int
  fixes q p :: nat
  assumes "q > p"
  shows "signed q (bw q (-(bw p a))) = -(bw p a)" (is "?lhs = ?rhs")  
  proof (cases "bw p a = 0")
    case False
      then have *: "(bw p a) > 0" 
        by (metis bw_def linorder_not_less mod_prop_mod nle_le take_bit_eq_mod take_bit_int_eq_self_iff)
      moreover have "(bw p a) \<le> 2^q"  
         using assms by (metis bw_def less_le_not_le reduce_mod take_bit_eq_mod take_bit_int_less_exp)
      moreover have "bw q (-(bw p a)) = 2^q -(bw p a)" 
         by (metis \<open>0 < bw p a\<close> bw_def calculation(2) take_bit_eq_mod take_bit_minus_small_eq)
      moreover have "bw q (2 * (- bw p a)) = bw q (2^q - 2* bw p a)" by (simp add: bw_def)
      moreover have "... = 2^q - 2*bw p a" proof -
        have "(bw p a) \<in> {1..2^p -1}" using bw_def bw_max_val * by auto
        then have **: "2 * (bw p a) \<in> {2..2^(p+1)-2}" by simp
        let ?set =  " {int(2^q) - int(2^(p+1)-2)..2^q - 2}"
        have ***: "2^q - 2 * (bw p a) \<in> ?set" using ** by simp
        have ****: "?set \<subseteq> {0..2^q - 1}" proof - 
           have "int(2^q) - int(2^(p+1)-2) > (0::int)"
             by (metis One_nat_def Suc_eq_plus1 Suc_leI assms diff_Suc_less diff_gt_0_iff_gt lessI less_imp_diff_less nat_less_le numeral_2_eq_2 of_nat_less_numeral_power_cancel_iff of_nat_numeral of_nat_power of_nat_zero_less_power_iff power_strict_increasing_iff zero_less_numeral) 
           then show ?thesis by simp
         qed
        then have "2^q - 2 * (bw p a) \<in> ..." using *** by blast
        then show ?thesis using bw_subset **** *** by presburger
      qed
      moreover have "signed q (bw q (-(bw p a))) =  2^q - 2*bw p a - (2^q - bw p a)" 
         by (metis add.inverse_inverse add_uminus_conv_diff arith_lemmas.mult_2 calculation(3,4,5) mod_prop_neg mod_prop_sub_left mod_prop_sub_right prop_two signed_def)
      moreover have "signed q (bw q (-(bw p a))) = - bw p a" 
         using calculation(6) by presburger
      ultimately show ?thesis by satx
  next
    case True  
    then show ?thesis using bw_0 signed_def by fastforce
qed

lemma signed_of_diff: 
  fixes a b :: int
  fixes q p r :: nat
  assumes "r > p" and "r > q"
  shows "signed r (bw r ((bw p a) - (bw q b))) = (bw p a) - (bw q b)" (is "?lhs = ?rhs")  
proof - 
  have lower_bound: "?rhs \<ge> -(2^q - 1)" using bw_def bw_max_val by (metis diff_0 diff_right_mono le_minus_iff minus_diff_eq order_trans pos_mod_sign zero_less_numeral zero_less_power) 
  moreover have upper_bound: "?rhs \<le> 2^p - 1" using bw_def bw_max_val by (metis diff_mono diff_zero take_bit_eq_mod take_bit_nonnegative) 
  ultimately have range: "?rhs \<in> {-(2^q - 1)..2^p - 1}" by auto
  show ?thesis proof(cases ?rhs "0::int" rule: linorder_cases)
    case less
    then have *: "?rhs \<in> {-(2^q - 1)..-1}" by (metis atLeastAtMost_iff diff_0 lower_bound zle_diff1_eq)
    then have "bw r ?rhs = bw r (2^r + ?rhs)" using bw_def by simp
    moreover have "2^r + ?rhs \<in> {2^r - 2^q + 1..2^r -1}" using * by auto
    moreover have "... \<subseteq> {0..2^r -1}" using assms(2) by auto
    ultimately have fact1: "bw r ?rhs = 2^r + ?rhs" using bw_subset by presburger

    have fact2: "bw r (2 * ?rhs) = 2^r + 2*?rhs" proof -
      have "2 * ?rhs \<in>  {-(2^(q+1) - 2)..-2}" using * bw_def bw_max_val by auto
      moreover have "bw r (2* ?rhs) = bw r (2^r + 2*?rhs)" using bw_def by auto
      moreover have "2^r + 2*?rhs \<in> {2^r - (2^(q+1) - 2)..2^r-2}" using calculation by simp
      moreover have "... \<subseteq> {0..2^r-1}" proof - 
         have "int(2^r) - int(2^(q+1)-2) > (0::int)" using assms(2)
           by (metis One_nat_def Suc_eq_plus1 Suc_leI diff_gt_0_iff_gt diff_less lessI less_imp_diff_less nat_less_le nat_zero_less_power_iff numeral_2_eq_2 of_nat_less_numeral_power_cancel_iff of_nat_numeral of_nat_power power_strict_increasing_iff zero_less_Suc) 
         then show ?thesis by simp
       qed
       ultimately show ?thesis using bw_subset by presburger
     qed
    then show ?thesis using signed_def bw_def fact1 fact2 mult_mod_left prop_two by auto
  next
    case equal
    then show ?thesis using bw_0 signed_def by auto
  next
    case greater
    then show ?thesis using signed_zext signed_def bw_def by (metis upper_bound assms(1) less_le_not_le take_bit_eq_mod take_bit_int_eq_self_iff zle_diff1_eq) 
  qed
qed
end
