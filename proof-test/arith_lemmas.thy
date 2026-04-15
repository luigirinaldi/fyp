theory arith_lemmas
    imports rewrite_defs 
begin

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

lemma mul_eq_prec:
"bw p (bw p a *  b) = bw p ( a * b)"
using mul_remove_prec by simp

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

lemma add_remove_prec_left:
"bw p (bw q a + b) = bw p (a + b)"
if "q \<ge> p"
by (metis bw_def le_imp_power_dvd mod_add_cong mod_mod_cancel that)

lemma add_remove_prec_right:
"bw p (a + (bw q b)) = bw p (a + b)"
if "q \<ge> p"
using add_remove_prec_left by (simp add: add.commute that)

lemma add_eq_prec:
"bw p (bw p a + b) = bw p (a + b)"
by (simp add: add_remove_prec_left)

lemma diff_left_remove_prec:
"bw p (bw q a - b) = bw p (a - b)"
if "q \<ge> p"
by (metis add_remove_prec_left add_uminus_conv_diff that)

lemma diff_left_eq_prec:
"bw p (bw p a - b) = bw p (a - b)"
using diff_left_remove_prec by simp

lemma diff_right_remove_prec:
"bw p (a - bw q b) = bw p (a - b)"
if "q \<ge> p"
by (metis bw_def le_imp_power_dvd mod_diff_cong mod_mod_cancel that)

lemma diff_right_eq_prec:
"bw p (a - bw p b) = bw p (a - b)"
using diff_right_remove_prec by simp

lemma reduce_mod:
"bw p (bw q a) = bw q a"
if "p \<ge> q"
using bw_def 
by (simp add: mod_exp_eq that)

lemma reduce_mod_bis:
"bw p (bw q a) = bw p a"
if "q \<ge> p"
using bw_def
by (simp add: mod_exp_eq that)

lemma mod_eq:
"bw p (bw p a) = bw p a"
using bw_def by simp

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

lemma mult_0: "0 * a = 0" for a :: int by simp
lemma mult_1: "1 * a = a" for a :: int by simp
lemma mult_2: "2 * a = a + a" for a ::int by simp
lemma add_0:  "0 + a = a" for a::int by simp
lemma diff_self: "a - a = 0" for a:: int by simp
lemma bw_1: "bw q 1 = 1" if "q > 0" using bw_def that by simp
lemma bw_0: "bw q 0 = 0" using bw_def by simp

lemma int_distrib: "a * (b + c) = (a * b) + (a * c)" for a b c ::int by algebra

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

lemma mul_by_bit: "(bw p ((bw q a) * (bw 1 b))) = (bw q a) * (bw 1 b)" if "p \<ge> q"
by (metis Suc_eq_plus1 antisym arith_lemmas.mult_1 bw_0 bw_def mod_eq mul_full_prec mult.commute not_less_eq_eq not_mod_2_eq_0_eq_1 power_one_right that times_int_code(1))

lemma mul_by_bit_eq:  "(bw p ((bw p a) * (bw 1 b))) = (bw p a) * (bw 1 b)" using mul_by_bit by blast

lemma mod_prop_sum: "(bw p (a + b)) = (bw p ((bw p a) + b))" using bw_def by presburger

lemma mod_prop_mul: "(bw p (a * b)) = (bw p ((bw p a) * b))" using bw_def by (simp add: mod_mult_right_eq mult.commute)

lemma mod_prop_sub_left: "(bw p (a - b)) = (bw p ((bw p a) - b))" using bw_def mod_prop_sum mod_diff_eq diff_left_eq_prec by presburger

lemma mod_prop_sub_right: "(bw p (a - b)) = (bw p (a - (bw p b)))" using bw_def mod_prop_sum mod_diff_eq diff_right_eq_prec by presburger

lemma mod_prop_or: "(bw p (or a b)) = (bw p (or (bw p a) b))" using bw_def by (metis mod_eq take_bit_int_def take_bit_or)

lemma mod_prop_and: "(bw p (and a b)) = (bw p (and (bw p a) b))" using bw_def by (metis mod_eq take_bit_and take_bit_eq_mod)

lemma mod_prop_xor: "(bw p (xor a b)) = (bw p (xor (bw p a) b))" using bw_def by (metis mod_eq take_bit_eq_mod take_bit_xor)

lemma mod_prop_not: "(bw p (not a)) = (bw p (not (bw p a)))" using bw_def by (metis take_bit_int_def take_bit_not_take_bit)

lemma mod_prop_neg: "(bw p (- a)) = (bw p (- (bw p a)))" using bw_def by (simp add: mod_minus_eq)

lemma mod_prop_mod: "(bw p a) = (bw p (bw p a))" using bw_def by auto

lemma div_1: 
fixes a :: int
shows "a div 1 = a" by simp

lemma div_floor_help: "(bw p a) div 2^p = 0" using bw_def by simp
lemma div_floor: "(bw p a) div b = 0" if "b \<ge> 2^p" using bw_def div_floor_help by (metis bw_max_val div_pos_pos_trivial leI not_exp_less_eq_0_int order.strict_trans2 pos_mod_sign that zle_diff1_eq)

lemma div_by_more: "(bw 1 a) div 2 = 0" using bw_def by simp

lemma shr_by_pos: "(a >> b) = a div (2^(nat(b)))" if "b > 0" using shr_def by simp

lemma shift_mod: 
fixes a b :: int
fixes p q :: nat
assumes "(p - q) \<ge> nat(b)" and "b > 0"
shows "bw q ((bw p a) >> b) = bw q (a >> b)" (is "?lhs = ?rhs")
proof - 
  have *: "?lhs = a mod 2 ^ p div 2 ^ nat b mod 2 ^ q" using bw_def shr_def by simp
  fix c :: int
  have div_mult: "c = (c * (2^nat b div 2^nat b))" by simp
  have "?lhs = (a * (2^nat b div 2^nat b)) mod (2 ^ p  * (2^nat b div 2^nat b)) div 2 ^ nat b mod 2 ^ q" using div_mult * by auto
  moreover have "... = ((a div 2^nat b) mod 2 ^ (p - nat b)) * (2^nat b) div 2 ^ nat b mod 2 ^ q" using assms mult_mod_left mult_exp_mod_exp_eq  by (simp add: div_exp_mod_exp_eq) 
  moreover have "... = ((a div 2^nat b) mod 2 ^ (p - nat b)) mod 2 ^ q" using div_mult by auto
  ultimately show ?thesis
  proof -
    have "\<not> b \<le> 0"
      using assms(2) by fastforce
    then have "nat b \<noteq> 0"
      using nat_0_iff by presburger
    then have "\<not> nat b \<le> 0"
      by blast
    then have "0 < nat b"
      by force
    then have "p - q \<noteq> 0"
      by (metis (no_types) assms(1) not_less)
    then have "\<not> p - q \<le> 0"
      by blast
    then have "0 < p - q"
      by fastforce
    then have "q \<le> p"
      by force
    then have "q \<le> p - nat b"
      by (metis (no_types) assms(1) diff_diff_cancel diff_le_mono2)
    then show ?thesis
      by (metis (full_types) \<open>a * (2 ^ nat b div 2 ^ nat b) mod (2 ^ p * (2 ^ nat b div 2 ^ nat b)) div 2 ^ nat b mod 2 ^ q = a div 2 ^ nat b mod 2 ^ (p - nat b) * 2 ^ nat b div 2 ^ nat b mod 2 ^ q\<close> \<open>a div 2 ^ nat b mod 2 ^ (p - nat b) * 2 ^ nat b div 2 ^ nat b mod 2 ^ q = a div 2 ^ nat b mod 2 ^ (p - nat b) mod 2 ^ q\<close> \<open>bw q (shr (bw p a) b) = a * (2 ^ nat b div 2 ^ nat b) mod (2 ^ p * (2 ^ nat b div 2 ^ nat b)) div 2 ^ nat b mod 2 ^ q\<close> assms(2) bw_def le_imp_power_dvd mod_mod_cancel shr_by_pos)
  qed 
qed

end