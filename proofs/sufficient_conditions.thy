(*

Log of work on this file:

11/01 18:50 start (plane otw to London)
      19:21 prooved up to mul_assoc including helper lemmas
      19:57 prooved add_assoc


*)

theory sufficient_conditions imports Main begin

definition "bw (p::nat) (a::int) = a mod 2^p"

value "bw 3 (-23)"

lemma bw_max_val:
"bw p a \<le> 2^p - 1"
by (simp add: bw_def)

theorem add_comm:
"bw r (bw p a + bw q b) = bw r (bw q b + bw p a)"
by (simp add: add.commute)

theorem mul_comm:
"bw r (bw p a * bw q b) = bw r (bw q b * bw p a)"
by (simp add: mult.commute)

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

(* found using try*)
lemma mul_remove_prec:
"bw p (bw q a *  b) = bw p ( a * b)"
if "q \<ge> p"
by (metis bw_def le_imp_power_dvd mod_mod_cancel mod_mult_cong that)

(* found using try after defining the helper lemmas*)
theorem mul_assoc:
"bw t (bw u (bw p a * bw r b) * bw s c) = bw t (bw p a * bw q (bw r b * bw s c))"
if "q \<ge> t \<or> (r+s) \<le> q" and "u \<ge> t \<or> (p+r) \<le> u"
by (smt (verit, del_insts) ab_semigroup_mult_class.mult_ac(1) mul_full_prec mul_remove_prec mult.commute that(1) that(2))

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

(* found using try*)
lemma add_remove_prec:
"bw p (bw q a + b) = bw p (a + b)"
if "q \<ge> p"
by (metis bw_def le_imp_power_dvd mod_add_cong mod_mod_cancel that)


(* found using try *)
theorem add_assoc:
"bw t (bw u (bw p a + bw r b) + bw s c) = bw t (bw p a + bw q (bw r b + bw s c))"
if "q \<ge> t \<or> (max r s) < q" and "u \<ge> t \<or> (max p r) < u"
by (smt (verit) add.commute add_full_prec add_remove_prec max_less_iff_conj that(1) that(2))