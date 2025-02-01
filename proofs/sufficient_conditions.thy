theory sufficient_conditions imports Main begin

definition "bw (p::nat) (a::int) = a mod 2^p"

value "bw 3 (-23)"

lemma bw_max_val:
"bw p a \<le> 2^p - 1"
using bw_def by simp

(* Bitvector Arithmetic Identities *)

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

(* found using try waiting approx 1 minute*)
(* no extra lemmas needed *)
theorem distribute_mult_over_add:
 "bw r (bw p a * bw q (bw s b + bw t c))
= bw r (bw u (bw p a * bw s b) + bw v (bw p a * bw t c))"
if "min q (min u v) \<ge> r"
by (smt (verit) add.commute add_remove_prec int_distrib(2) min.boundedE mul_remove_prec mult.commute that)

theorem sum_same:
"bw q (bw p a + bw p a) = bw q (bw 2 2 * bw p a)" 
using bw_def by fastforce

(* needed some nudging along *)
theorem mult_sum_same:
"bw r (bw s (bw p a * bw q b) + bw q b) = bw r (bw t (bw p a + bw 1 1) * bw q b)"
if "t > p" and "s \<ge> p + q" and "p >0"
proof -
have "t > p \<and> t > 1" using nat_neq_iff that(1) that(3) by blast
moreover have "bw t (bw p a + bw 1 1) = (bw p a + bw 1 1)" using add_full_prec calculation by blast
ultimately show ?thesis by (metis bw_def int_distrib(1) less_add_one less_numeral_extra(1) mod_pos_pos_trivial mul_full_prec mult_1 one_add_one power_0 power_strict_increasing that(2) zero_less_one_class.zero_le_one)
qed

theorem add_zero:
"bw p (bw p a + bw q b) = bw p a"
if "bw p 0 = bw p b"
using bw_def that by (metis add.commute add_remove_prec mod_0 nle_le plus_int_code(2))

theorem sub_to_neg:
"bw r (bw p a - bw q b) = bw r (bw p a + -(bw q b))"
by simp

(* using sledgehammer and "using bw_def" *)
theorem mult_by_one:
"bw p (bw p a * bw q b) = bw p a"
if "bw p 1 = bw p b" and "p > 0" and "q > 0"
using bw_def by (smt (verit, best) le_imp_power_dvd mod_mod_cancel mul_remove_prec mult.commute mult_cancel_right1 one_mod_2_pow_eq power_increasing_iff that(1) that(2) that(3))

lemma reduce_mod:
"bw p (bw q a) = bw q a"
if "p \<ge> q"
using bw_def 
by (smt (verit) bw_max_val mod_pos_pos_trivial pos_mod_sign power_increasing that zero_less_power)

(* assuming b can always be cast to a nat *)
definition "shl (a::int) (b::int) = a * 2^(nat(b))"
definition "shr (a::int) (b::int) = a div 2^(nat(b))"
value "nat(-3)"
value "shl (-3) (-3)"
value "shl (bw 2 3) (bw 3 (3))"
value "shr (bw 8 48) (bw 3 (3))"

(* using try *)
theorem mult_by_two:
"bw r (bw p a * bw 2 2) = bw r(shl (bw p a) 1)"
using bw_def shl_def by force

(* Bitvector logic identities *)

(* manual proof *)
theorem merge_left_shift:
"bw r (shl (bw u (shl (bw p a) (bw q b))) (bw s c)) = bw r (shl (bw p a) (bw t (bw q b + bw s c)))" (is "?lhs = ?rhs")
if "t > max q s" and "u \<ge> r"
proof - 
have "?lhs = bw r ((bw p a * 2 ^ nat(bw q b)) * 2 ^ nat(bw s c))" using  add.right_neutral add_remove_prec that(2) mul_remove_prec shl_def by presburger
moreover have "... = bw r(bw p a * 2 ^(nat(bw q b + bw s c)))" by (simp add: bw_def mult.commute mult.left_commute nat_add_distrib power_add)
moreover have "... = ?rhs" using add_full_prec that(1) shl_def by simp
ultimately show ?thesis by simp
qed

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

(* sledgehammer cannot solve it*)
theorem merge_right_shift:
"bw r (shr (bw u (shr (bw p a) (bw q b))) (bw s c)) = bw r (shr (bw p a) (bw t (bw q b + bw s c)))" (is "?lhs = ?rhs")
if "t > max q s" and "u \<ge> p"
proof - 
have "?lhs = bw r ((bw u ((bw p a) div (2 ^ nat(bw q b)))) div 2 ^nat(bw s c))" using shr_def by auto
moreover have "... =  bw r ( ((bw p a) div (2 ^ nat(bw q b))) div 2 ^nat(bw s c)) " using that(2) div_gte by auto
moreover have "... = bw r ((bw p a) div (2 ^ nat(bw q b) * 2^nat(bw s c)))" by (simp add: div_exp_eq power_add)
ultimately show ?thesis by (metis add_full_prec bw_def max_less_iff_conj nat_add_distrib not_exp_less_eq_0_int pos_mod_sign power_add shr_def that(1) verit_comp_simplify1(3))
qed

(* proven by sledgehammer*)
theorem left_shift_add:
"bw r ((shl (bw s (bw p a + bw q b)) (bw t c))) = bw r ((bw u (shl (bw p a) (bw t c))) + (bw u (shl (bw q b) (bw t c))))"
if "s \<ge> r \<or> s > max p q" and "u \<ge> r"
using shl_def by (smt (verit, ccfv_SIG) add.commute add_full_prec add_remove_prec int_distrib(1) max_less_iff_conj mul_remove_prec that(1) that(2))

(* sledgehammer *)
theorem left_shift_mult:
"bw r ((shl (bw t (bw p a * bw q b)) (bw t c))) = bw r (bw v (shl (bw p a) (bw t c)) * (bw q b))" 
if "v \<ge> r" and "t \<ge> r"
using shl_def by (metis ab_semigroup_mult_class.mult_ac(1) mul_remove_prec mult.commute that(1) that(2))

theorem add_right_shift:
"bw r (
    (bw p a)
    + 
  bw q (
    (shr (bw t b) (bw u c))
  )
) 
= 
bw r (
  shr 
    (bw v 
      (
        (bw s (shl (bw p a) (bw u c)))
        + 
        (bw t b)
      )
    ) 
    (bw u c)
  )" (is "?lhs = ?rhs")
  if "q \<ge> t" and "v > max s t" and "s \<ge> p + 2^u - 1" and "u > 0"
proof - 
have "?lhs = bw r ((bw p a) + (bw q ((bw t b) div 2^nat(bw u c))))" using shr_def by simp
moreover have "... =  bw r (((bw p a) * 2^nat(bw u c)) div 2^nat(bw u c)  + (bw q ((bw t b) div 2^nat(bw u c))))" by simp
(* found by simp after introducing the above step of multiplying and dividing by the same number *) 
moreover have "... = ?rhs" by (smt (verit, del_insts) add_full_prec calculation(2) div_gte div_mult_self1 max.strict_boundedE mul_pow2 power_eq_0_iff shl_def shr_def that(1) that(2) that(3))
ultimately show ?thesis by argo
qed


