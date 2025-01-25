(*

Log of work on this file:

11/01 18:50 start (plane otw to London)
      19:21 prooved up to mul_assoc including helper lemmas
      19:57 prooved add_assoc
      20:20 landed and stopped at sub_to_neg
12/01 15:40 start
      15:56 finished bitvector arithmetic identities
      16:02 stopped as isabelle not accepting output of mod as input to 2^(?a)
*)

theory sufficient_conditions imports Main begin

definition "bw (p::nat) (a::int) = a mod 2^p"

value "bw 3 (-23)"

lemma bw_max_val:
"bw p a \<le> 2^p - 1"
by (simp add: bw_def)

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

definition "shl (a::int) (b::int) = a * 2^b"
value "shl (-3) 3"
value " (-3)"

(* using try *)
theorem mult_by_two:
"bw r (bw p a * bw 2 2) = bw r(shl (bw p a) 1)"
using bw_def shl_def by force

(* Bitvector logic identities *)
theorem merge_left_shift:
"bw r (shl (bw u (shl (bw p a) (bw q b))) (bw s c)) = bw r (shl (bw p a) bw t (bw q b + bw s c))"


