theory rewrite_lemmas
    imports rewrite_defs 
begin

(* Arithmetic lemmas *)

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

lemma add_remove_prec:
"bw p (bw q a + b) = bw p (a + b)"
if "q \<ge> p"
by (metis bw_def le_imp_power_dvd mod_add_cong mod_mod_cancel that)

lemma add_eq_prec:
"bw p (bw p a + b) = bw p (a + b)"
by (simp add: add_remove_prec)

lemma diff_left_remove_prec:
"bw p (bw q a - b) = bw p (a - b)"
if "q \<ge> p"
by (metis add_remove_prec add_uminus_conv_diff that)

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
by (smt (verit) bw_max_val mod_pos_pos_trivial pos_mod_sign power_increasing that zero_less_power)

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

lemma bw_1: "bw q 1 = 1" if "q > 0" using bw_def that by simp
lemma bw_0: "bw q 0 = 0" using bw_def by simp

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

(* Bitwise operations *)

lemma "bw q (or (bw p a) (bw r b)) = or (bw p a) (bw r b)" if "q \<ge> p" and "q >= r"
by (metis bw_def reduce_mod take_bit_eq_mod take_bit_or that) 

lemma add_as_xor_and: "bw p a + bw q b = xor (bw p a) (bw q b) + 2 * (and (bw p a) (bw q b))"
for p q :: nat and a b c :: int
by (smt (verit) and.commute and.left_commute and.right_neutral and_eq_not_not_or bit.conj_disj_distrib 
    bit.conj_disj_distrib2 bit.conj_xor_distrib2 bit.xor_cancel_left bit.xor_def bit.xor_def2 bit.xor_one_left 
    bit.xor_one_right or.idem or_eq_not_not_and plus_and_or xor.assoc xor.right_neutral)

lemma xor_as_or_and: "xor (bw p a) (bw q b) = (or (bw p a) (bw q b)) - (and (bw p a) (bw q b))" 
by (smt (verit, ccfv_SIG) add_as_xor_and plus_and_or)

lemma neg_not: "-(bw p a) = (not (bw p a)) + 1" by (simp only: minus_eq_not_plus_1)

(* Bitwise identities *)

(* value "xor (bw 1 (-1)) (bw 1 (-1))"
value "(bw 1 (not (bw 1 (-1))))" *)

(* sledgehammer_params[timeout = 300] *)

(* lemma "bw p (xor (bw p a) (bw p (-1))) = bw p (not (bw p a))" if "p > 0"
sorry *)

lemma and_allones: "and (bw p a) (bw p (-1)) = (bw p a)"
    by (metis and.right_neutral bw_def take_bit_and take_bit_eq_mod)
lemma or_allones: "or (bw p a) (bw p (-1)) = bw p (-1)"
    by (metis bit.disj_one_right bw_def take_bit_int_def take_bit_or)
lemma xor_allones: "(bw p (xor a (bw p (-1)))) = (bw p (not a))" 
    by (metis bit.xor_one_right bw_def mod_eq take_bit_eq_mod take_bit_xor)

lemma and_zero: "and a 0 = 0" by (simp only: Bit_Operations.semiring_bit_operations_class.and_zero_eq)
lemma or_zero: "or a 0 = a" by (simp only: Bit_Operations.semiring_bit_operations_class.or.comm_neutral)

(* lemma not_not: "a = not (not a)" for a :: int by simp *)
lemma and_remove: "(bw p (and (bw p a) (bw p b))) = (and (bw p a) (bw p b))" by (simp add: bw_def)
lemma or_remove: "(bw p (or (bw p a) (bw p b))) = (or (bw p a) (bw p b))" by (simp add: OR_upper bw_def)
lemma xor_remove: "(bw p (xor (bw p a) (bw p b))) = (xor (bw p a) (bw p b))" by (simp add: XOR_upper bw_def)

lemma demorg_and: "(bw p (not (and (bw p a) (bw p b)))) = bw p (or (bw p (not (bw p a))) (bw p (not (bw p b))))" using bw_def by (metis bit.de_Morgan_conj or_remove take_bit_eq_mod take_bit_or)
lemma demorg_or: "(bw p (not (or (bw p a) (bw p b)))) = bw p (and (bw p (not (bw p a))) (bw p (not (bw p b))))" using bw_def by (metis and_remove bit.de_Morgan_disj take_bit_and take_bit_eq_mod)

lemma and_assoc: "(and (and a b) c) = (and c (and b a))" by (simp add: and.commute)
lemma or_assoc: "(or (or a b) c) = (or c (or b a))" by (simp add: or.commute)
lemma not_bw_not: "bw p (not (bw p (not (bw p a)))) = (bw p a)" if "p>0" by (metis bit.double_compl bw_def take_bit_int_def take_bit_not_take_bit)

lemma and_distrib: "and a (or b c) = or (and a b) (and a c)" for a b c :: int by (simp only: Bit_Operations.ring_bit_operations_class.bit.conj_disj_distrib and.commute)

lemma xor_and_or_help: "and (or a b) (or (not a) (not b)) = xor a b" for a b :: int by (simp add: bit.xor_def2)

lemma xor_and_or: "and (or (bw p a) (bw p b)) (or (bw p (not (bw p a))) (bw p (not (bw p b)))) = xor (bw p a) (bw p b)" for a b :: int 
using xor_and_or_help by (metis bw_def take_bit_and take_bit_eq_mod take_bit_not_take_bit take_bit_or take_bit_xor)

lemma and_self: "and a a = a" by simp
lemma or_self: "or a a = a" by simp
lemma and_not_self: "(and (bw p a) (bw p (not (bw p a)))) = 0" by (metis bit.xor_self or_self xor_and_or)
lemma or_not_self: "(or (bw p a) (bw p (not (bw p a)))) = bw p (-1)" by (metis bit.disj_cancel_right bw_def take_bit_eq_mod take_bit_not_take_bit take_bit_or)

end