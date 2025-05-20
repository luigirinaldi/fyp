theory rewrite_lemmas
    imports Main
begin



definition "bw (p::nat) (a::int) = a mod 2^p"
text "sign extension by interpreting as two's compl and then casting"
definition "sext (p::nat) (q::nat) (a::int) = bw q (bw p (2 * a) - bw p a)"

(* assuming b can always be cast to a nat *)
definition "shl (a::int) (b::int) = a * 2^(nat(b))"
definition "shr (a::int) (b::int) = a div 2^(nat(b))"
(* 
    Arithmetic right shift, if the shift doesn't underflow then sign
    extend the shifted down value. Otherwise sign extend the top bit of a 
*)
definition ashr :: "nat => int => int => int"
where "ashr p a b = 
        (if (b < int p)
        then sext (p - nat b) p (shr (bw p a) b)
        else sext 1 p (shr (bw p a) (int p -1)))"

value "ashr 5 (-10) 2"

syntax
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
lemma bw_p_0: "bw 0 p = 0" using bw_def by simp

lemma sub_to_neg: "(a::int) - b = a + -1 * b" by simp

lemma div_div_simp: "((a::int) div b) div c = a div (b * c)" if "a > 0" and "b > 0" and "c >0"
by (metis nless_le that(3) zdiv_zmult2_eq)

lemma bw_pow_sum: "a ^ nat (bw p b) * a ^ nat (bw q c) = a ^ nat (bw p b + bw q c)"
for a b c :: int and p q :: nat 
by (simp add: bw_def nat_add_distrib power_add) 

lemma div_pow_join: "(a div b) div c = a div (b * c)"
if "c > 0"
for a b c :: int
using that zdiv_zmult2_eq by simp

lemma div_same: "a * b div a = b" 
if "a > 0" 
for a::int 
using that by force 

lemma div_mult_self: "(a + b * c) div b = a div b + c" if "b \<noteq> 0" for a::int 
using that by simp

lemma move_pow2_mod: "((2 ^ p) * a) mod 2 ^ q = 2 ^ p * (a mod 2 ^ (q -p))" if "q >= p" for a::int and p q :: nat
by (simp add: mult.commute mult_exp_mod_exp_eq that)

lemma div_remove_mod: "((bw p a) div 2 ^ q) mod 2 ^ (p - q) = ((bw p a) div 2 ^ q)" if "p >= q"
by (simp add: bw_def div_exp_mod_exp_eq that)

lemma "bw k ((int k) -1) = (int k) - 1" if "k > 0" for k :: nat
proof - 
have "(int k - 1) >= 0" using that by simp
then show ?thesis using bw_def by (smt (verit, ccfv_SIG) dbl_simps(3) dbl_simps(5) dual_order.refl int_ops(2) mod_pos_pos_trivial numerals(1) of_nat_numeral of_nat_power_le_of_nat_cancel_iff self_le_ge2_pow)
qed

end