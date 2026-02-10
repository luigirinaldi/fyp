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


lemma signed_of_neg: 
  fixes a :: int
  fixes p :: nat
  assumes "q > p"
  shows "signed q (bw q (-(bw p a))) = -(bw p a)" (is "?lhs = ?rhs")
proof -
  have "?lhs = bw q (2 * (bw (q - 1) (bw q (- (bw p a))))) - bw q (bw q (-(bw p a)))" apply (simp only: signed_def) done
  moreover have "... =  bw q ((bw (q - 1 + 1) (2* (bw q (- (bw p a)))))) - bw q (bw q (-(bw p a)))" using bw_def mult_mod_left power_eq_if by auto
  moreover have "... = bw q ((bw q (bw (q + 1) (2* (- (bw p a)))))) - bw q (bw q (-(bw p a)))" using bw_def prop_two by (metis add_diff_cancel_right')
  moreover have "... = bw q (2* (- (bw p a))) - bw q (-(bw p a))" using reduce_mod reduce_mod_bis by auto
  ultimately show ?thesis proof cases
    assume "(bw p a) > 0"
      then have "- (bw p a) < 0" by linarith
      moreover have "(bw p a) \<le> 2^q" using assms by (metis bw_def less_le_not_le reduce_mod take_bit_eq_mod take_bit_int_less_exp)
      moreover have "bw q (-(bw p a)) = 2^q -(bw p a)" by (metis \<open>0 < bw p a\<close> bw_def calculation(2) take_bit_eq_mod take_bit_minus_small_eq) 
      moreover have "bw q (2* (- bw p a)) = bw q ((- bw p a) + (- bw p a))" by auto
      ultimately show ?thesis by (smt (verit, ccfv_threshold) \<open>signed q (bw q (- bw p a)) = bw q (2 * bw (q - 1) (bw q (- bw p a))) - bw q (bw q (- bw p a))\<close> add_full_prec assms bw_def minus_mod_self2 mod_pos_pos_trivial prop_two)
    next 
      show ?thesis by (smt (verit, ccfv_threshold) \<open>bw q (2 * bw (q - 1) (bw q (- bw p a))) - bw q (bw q (- bw p a)) = bw q (bw (q - 1 + 1) (2 * bw q (- bw p a))) - bw q (bw q (- bw p a))\<close>
            \<open>bw q (bw (q - 1 + 1) (2 * bw q (- bw p a))) - bw q (bw q (- bw p a)) = bw q (bw q (bw (q + 1) (2 * - bw p a))) - bw q (bw q (- bw p a))\<close> \<open>signed q (bw q (- bw p a)) = bw q (2 * bw (q - 1) (bw q (- bw p a))) - bw q (bw q (- bw p a))\<close>
            add_full_prec assms bw_def le_add1 less_le_not_le mod_prop_neg reduce_mod reduce_mod_bis zmod_zminus1_eq_if) 
  qed
qed
end
