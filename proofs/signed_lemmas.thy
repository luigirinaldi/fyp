theory signed_lemmas
  imports rewrite_defs
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

end
