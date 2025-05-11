theory rewrite_lemmas
    imports Main 
begin

definition "bw (p::nat) (a::int) = a mod 2^p"
(* assuming b can always be cast to a nat *)
definition "shl (a::int) (b::int) = a * 2^(nat(b))"
definition "shr (a::int) (b::int) = a div 2^(nat(b))"
syntax
    (* The function is defined above *)
    "shl" :: "int => int => int" ("_ << _")
    "shr" :: "int => int => int" ("_ >> _")


lemma bw_max_val:
"bw p a \<le> 2^p - 1"
using bw_def by simp

lemma mul_full_prec:
"bw p (bw q a * bw r b) = (bw q a * bw r b)"
if "q + r \<le> p"
proof -
have "bw q a * bw r b \<le> (2^q - 1) * (2^r - 1)" using bw_def bw_max_val by (simp add: mult_mono)
(* found with try *)
also have "... < 2^(q + r)" by (smt (verit, best) distrib_left left_diff_distrib' mult_mono one_le_power one_power2 power_add)
(* found with try *)
then show ?thesis by (smt (verit, ccfv_SIG) bw_def calculation mod_pos_pos_trivial mult_nonneg_nonneg pos_mod_sign power_increasing that zero_less_power)
qed

lemma mul_remove_prec:
"bw p (bw q a *  b) = bw p ( a * b)"
if "q \<ge> p"
by (metis bw_def le_imp_power_dvd mod_mod_cancel mod_mult_cong that)

lemma add_full_prec:
"bw p (bw q a + bw r b) = (bw q a + bw r b)"
if "q < p \<and> r < p"
proof -
have "bw q a + bw r b \<le> (2^q - 1) + (2^r - 1)" using bw_def bw_max_val by (meson add_mono)
(* found with try *)
moreover have "... \<le> (2^(p-1) - 1) + (2^(p-1) - 1)" using that by (metis ab_group_add_class.ab_diff_conv_add_uminus add_le_imp_le_diff add_mono add_right_mono less_iff_succ_less_eq one_le_numeral power_increasing)
moreover have "... < 2^p" by (simp add: power_eq_if)
ultimately show ?thesis by (simp add: bw_def)
qed

lemma add_remove_prec:
"bw p (bw q a + b) = bw p (a + b)"
if "q \<ge> p"
by (metis bw_def le_imp_power_dvd mod_add_cong mod_mod_cancel that)

lemma reduce_mod:
"bw p (bw q a) = bw q a"
if "p \<ge> q"
using bw_def 
by (smt (verit) bw_max_val mod_pos_pos_trivial pos_mod_sign power_increasing that zero_less_power)


lemma div_gte:
"bw p ((bw q a) div 2^nat(bw r b)) = bw q a div 2^nat(bw r b)"
if "p \<ge> q"
proof - 
have "(bw q a) div 2^nat(bw r b) \<le> 2^q - 1" using bw_max_val bw_def by (smt (verit) div_by_1 pos_imp_zdiv_nonneg_iff zdiv_mono2 zero_less_power)
moreover have "... < 2^p" using that(1) by (smt (verit) power_increasing)
ultimately show ?thesis by (simp add: bw_def pos_imp_zdiv_nonneg_iff)
qed

lemma mul_pow2:
"bw s (bw p a * 2^nat(bw q b)) = bw p a * 2^nat(bw q b)"
if "s \<ge> p + 2^q -1"
proof - 
have "(bw p a * 2^nat(bw q b)) \<le> (2^p - 1)*(2^(2^q - 1))" using bw_def bw_max_val by (metis add_le_imp_le_diff diff_ge_0_iff_ge less_iff_succ_less_eq mult_mono nat_less_numeral_power_cancel_iff one_le_numeral one_le_power power_increasing zero_le_numeral zero_le_power zle_diff1_eq)
moreover have "... \<le> 2^(p + 2^q - 1) - 2^(2^q - 1)" by (metis (no_types, opaque_lifting) Nat.add_diff_assoc add_le_imp_le_diff diff_add_cancel left_diff_distrib' mult_1 nle_le one_le_numeral one_le_power power_add)
moreover have "... \<le> 2^(p + 2^q - 1)" by simp
moreover have "... \<le> 2^s" using that(1) by simp
ultimately show ?thesis by (smt (verit) bw_def mod_pos_pos_trivial mult_nonneg_nonneg one_le_power pos_mod_sign)
qed

lemma bw_1: "bw q 1 = 1" if "q > 0" using bw_def that by simp
lemma bw_0: "bw q 0 = 0" using bw_def by simp

lemma sub_to_neg: "(a::int) - b = a + -1 * b" by simp


end