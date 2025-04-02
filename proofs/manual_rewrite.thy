theory manual_rewrite
    imports rewrite_lemmas 
begin

(* Bitvector Arithmetic Identities *)
theorem add_comm:
"bw r (bw p a + bw q b) = bw r (bw q b + bw p a)"
by (simp add: add.commute)

theorem mul_comm:
"bw r (bw p a * bw q b) = bw r (bw q b * bw p a)"
by (simp add: mult.commute)

(* found using try after defining the helper lemmas*)
theorem mul_assoc:
"bw t (bw u (bw p a * bw r b) * bw s c) = bw t (bw p a * bw q (bw r b * bw s c))"
if "q \<ge> t \<or> (r+s) \<le> q" and "u \<ge> t \<or> (p+r) \<le> u"
by (smt (verit, del_insts) ab_semigroup_mult_class.mult_ac(1) mul_full_prec mul_remove_prec mult.commute that(1) that(2))

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
(* found by simp after introducing the step of multiplying and dividing by the same number *) 
moreover have "... = ?rhs" by (smt (verit, del_insts) add_full_prec calculation(2) div_gte div_mult_self1 max.strict_boundedE mul_pow2 power_eq_0_iff shl_def shr_def that(1) that(2) that(3))
ultimately show ?thesis by argo
qed


lemma remove_ext:
"bw r (ext r (bw q ( ext q (bw p b) + ext q (bw p c)))) = bw r (ext r (bw p b) + ext r (bw p c))"
if "p < q" and "q < r"
 proof -
   have f1: "\<forall>i. (i::int) mod 2 ^ q = i mod 2 ^ q mod 2 ^ r"
   by (metis (no_types) add_full_prec bw_def comm_monoid_add_class.add_0 mod_0 that(2))
   have "\<forall>i. (i::int) mod 2 ^ p mod 2 ^ q = i mod 2 ^ p"
   by (metis (no_types) add_full_prec bw_def comm_monoid_add_class.add_0 mod_0 that(1))
   then show ?thesis
   using f1 by (metis (no_types) add_diff_cancel_left' add_full_prec bw_def ext_def mult_2 that(1) that(2))
qed

theorem assoc_sign_extend:  
"bw r ( ext r (bw p a) + (ext r (bw q ( ext q (bw p b) + ext q (bw p c))))) =
 (bw r ( ext r (bw q ( ext q (bw p a) + ext q (bw p b)))  + ext r (bw p c)))" 
 if "p < q" and "q < r" (*
 by (smt (verit) add.left_commute add_diff_cancel_left' add_full_prec bw_def ext_def less_or_eq_imp_le mod_add_left_eq mult_2 order_trans reduce_mod that(1) that(2))
 *)
 proof - 
 have *: "bw r (ext r (bw q ( ext q (bw p b) + ext q (bw p c)))) = bw r (ext r (bw p b) + ext r (bw p c))" using remove_ext that(1) that(2) by blast
 moreover have **:  "bw r (ext r (bw q ( ext q (bw p a) + ext q (bw p b)))) = bw r (ext r (bw p a) + ext r (bw p b))" using remove_ext that(1) that(2) by blast
 ultimately show ?thesis by (metis ab_semigroup_add_class.add_ac(1) add.commute bw_def mod_add_left_eq)
 qed

lemma add_bw: "bw a (b + c) = bw a ( (bw a b) + bw a c)"  using bw_def by presburger
lemma ext_equiv: "bw r (ext q (bw p b)) = bw r (ext r (bw p b))" if "q \<ge> r" and "p \<ge> r" 
proof -
have f1: "\<forall>i ia ib. (ib::int) + (i + (ia + - ib)) = i + ia"
by fastforce
have f2: "\<forall>i ia ib. (ib::int) + i = ia + (ib + (- ia + i))"
by force
then have f3: "\<forall>i ia ib ic. ((i::int) + ia) mod ic = (ib + (i + (- (ib mod ic) + ia))) mod ic"
by (metis (no_types) mod_add_left_eq)
have f4: "\<forall>i ia ib. ((ib::int) + - ia) mod i = (ib + - (ia mod i)) mod i"
using f2 f1 by (metis (no_types) mod_add_left_eq)
have "(2 * (b mod 2 ^ p) + - (b mod 2 ^ p)) mod 2 ^ r = (2 * (b mod 2 ^ p) + - (b mod 2 ^ p mod 2 ^ q)) mod 2 ^ r"
using f3 f1 by (metis (full_types) add_remove_prec bw_def that(1))
then show ?thesis
using f4 by (metis (full_types) add_remove_prec add_uminus_conv_diff bw_def ext_def mod_add_left_eq that(1))
qed


theorem assoc_sign_extend_2:
"bw r ( ext r (bw p a) + (ext r (bw q ( ext q (bw p b) + ext q (bw p c))))) =
 (bw r ( ext r (bw q ( ext q (bw p a) + ext q (bw p b)))  + ext r (bw p c)))" 
 if "q \<ge> r" and "p \<ge> r" 
 proof -
 (*have *: "bw r (ext r (bw p a)) = bw r (ext p (bw p a))" by (smt (verit, best) add_remove_prec add_uminus_conv_diff bw_def ext_def mod_diff_right_eq nle_le reduce_mod that(2)) 
 moreover have **: "bw r (ext r (bw q d)) = bw r (ext q (bw q d))" by (smt (verit) add_remove_prec add_uminus_conv_diff bw_def ext_def le_refl mod_diff_right_eq reduce_mod that(1))
*)
have "bw r ( ext r (bw p a) + (ext r (bw q ( (ext q (bw p b)) + ext q (bw p c) ))) ) =
      bw r ((bw r (ext r (bw p a))) + bw r (ext r (bw q ( (ext q (bw p b)) + ext q (bw p c)))))" using bw_def add_bw by simp
moreover have "... = 
     bw r ((bw r (ext r (bw p a))) + bw r (ext r (bw r (bw q ( (ext q (bw p b)) + ext q (bw p c))))))" using ext_def bw_def by (metis mod_mod_trivial mod_mult_eq)
moreover have "... = 
     bw r ((bw r (ext r (bw p a))) + bw r (ext r (bw r ( (ext q (bw p b)) + ext q (bw p c)))))" using ext_def bw_def that(1)  by (metis le_imp_power_dvd mod_mod_cancel)
 moreover have "... = 
     bw r ((bw r (ext r (bw p a))) + bw r (ext r (bw r ( bw r (ext q (bw p b)) + bw r (ext q (bw p c))))))" using add_bw by presburger
 moreover have "... = 
     bw r ((bw r (ext r (bw p a))) + bw r (ext r (bw r ( bw r (ext r (bw p b)) + bw r (ext r (bw p c))))))" using bw_def ext_def ext_equiv that by presburger
 moreover have "... = bw r (ext r (bw p a) + (ext r (bw p b)) + (ext r (bw p c)))" 
     proof -
     have "\<And>n i. ext n i mod 2 ^ n = i mod 2 ^ n"
     by (metis (no_types) add_diff_cancel_right' add_uminus_conv_diff ext_def mod_add_left_eq mod_diff_right_eq mult_2)
     then show ?thesis
     by (metis add.commute add.left_commute bw_def mod_add_right_eq)
     qed

have "bw r ( ext r (bw q ( ext q (bw p a) + ext q (bw p b)))  + ext r (bw p c)) =
      bw r ( bw r (ext r (bw q ( ext q (bw p a) + ext q (bw p b))))  + bw r (ext r (bw p c)))" using bw_def add_bw by simp
moreover have "... = 
      bw r ( bw r (ext r (bw r ( ext q (bw p a) + ext q (bw p b))))  + bw r (ext r (bw p c)))" using ext_def bw_def by (smt (verit, best) le_imp_power_dvd mod_add_cong mod_mod_cancel mod_mod_trivial mult_2 that(1))
      moreover have "... = 
      bw r ( bw r (ext r (bw r ( ext r (bw p a) + ext r (bw p b))))  + bw r (ext r (bw p c)))" using ext_def add_bw ext_equiv that by metis
      moreover have "... = bw r (  ext r (bw p a) + ext r (bw p b)  + (ext r (bw p c)))" 
      proof -
       have "\<And>n i. ext n i mod 2 ^ n = i mod 2 ^ n"
       by (metis (no_types) add_diff_cancel_right' add_uminus_conv_diff ext_def mod_add_left_eq mod_diff_right_eq mult_2)
       then show ?thesis
       by (metis add.commute add.left_commute bw_def mod_add_right_eq)
       qed

       ultimately show ?thesis using \<open>bw r (bw r (ext r (bw p a)) + bw r (ext r (bw r (bw r (ext r (bw p b)) + bw r (ext r (bw p c)))))) = bw r (ext r (bw p a) + ext r (bw p b) + ext r (bw p c))\<close> by argo
qed
end


