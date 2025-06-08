theory testproofs
    imports rewrite_lemmas
begin

lemma "(-a * (2^(c-1)) + b) mod 2^c = (a * (2^(c-1)) + b) mod 2^c" 
if "a \<in> {0,1}" and "c > 0"
for a b :: int and c :: nat
proof - 
have "(-a * (2^(c-1)) + b) mod 2^c = (a * (2^c) - a * (2^(c-1)) + b) mod 2^c" by (metis ab_group_add_class.ab_diff_conv_add_uminus add.assoc mod_mult_self3 mult_minus_left)
moreover have "a * (2^c) - a * (2^(c-1)) = a * 2^(c-1)" by (metis Suc_pred' add_implies_diff mult_2_right power_Suc power_commutes right_diff_distrib' that(2))
ultimately show ?thesis by argo
qed

lemma not_not: "a = not (not a)" for a :: int by simp
lemma and_remove: "(bw p (and (bw p a) (bw p b))) = (and (bw p a) (bw p b))" by (simp add: bw_def)
lemma or_remove: "(bw p (or (bw p a) (bw p b))) = (or (bw p a) (bw p b))" by (simp add: OR_upper bw_def)
lemma xor_remove: "(bw p (xor (bw p a) (bw p b))) = (xor (bw p a) (bw p b))" by (simp add: XOR_upper bw_def)
lemma demorg_and: "not (and a b) = or (not a) (not b)" by simp
lemma demorg_or: "not (or a b) = and (not a) (not b)" by simp

lemma xor_allones: "(bw p (xor a (bw p (-1)))) = (bw p (not a))" by (metis bit.xor_one_right bw_def mod_eq take_bit_eq_mod take_bit_xor)
lemma and_assoc: "(and (and a b) c) = (and c (and b a))" by (simp add: and.commute)

lemma not_bw_not: "bw p (not (bw p (not (bw p a)))) = (bw p a)" if "p>0" by (metis bit.double_compl bw_def take_bit_int_def take_bit_not_take_bit)


theorem add_comm:
"(bw r ((bw p a) + (bw q b))) = (bw r ((bw q b) + (bw p a)))" (is "?lhs = ?rhs")
proof - 
have "?lhs = ?rhs" 
    apply (simp add: add.commute)
    done
then show ?thesis by blast
qed
(* by (simp add: add.commute)
then show ?thesis by simp
qed *)


text "Proof produced by the tool: 
    (bw r (* (bw p a) 2))
    (bw r (* (bw p a) (Rewrite<= src/language.rs:109:20 (^ 2 1))))
    (bw r (Rewrite<= left-shift (<< (bw p a) 1)))
    (bw r (<< (bw p a) 1))
"
theorem mul_two:
"(bw r ((bw p a) * 2)) = (bw r (shl (bw p a) 1))" (is "?lhs = ?rhs")
proof - 
(* have "?rhs = (bw r ((bw p a) * (2^1)))" 
    apply (simp add: shl_def) *)
have "?rhs = ?lhs" 
    apply (simp add: shl_def)
    done
then show ?thesis by simp
qed

text "
Tool explanation out:
    lhs:(bw t (+ (bw u (+ (bw p a) (bw r b))) (bw s c)))
    rhs:(bw t (+ (bw p a) (bw q (+ (bw r b) (bw s c)))))
    conditions:['(>= q t)', '(>= u t)']

    (bw t (+ (bw u (+ (bw p a) (bw r b))) (bw s c)))
    (Rewrite=> mod-sum (bw t (+ (+ (bw p a) (bw r b)) (bw s c))))
    (bw t (Rewrite=> add-assoc (+ (bw p a) (+ (bw r b) (bw s c)))))
    (bw t (Rewrite=> add-comm (+ (+ (bw r b) (bw s c)) (bw p a))))
    (Rewrite<= mod-sum (bw t (+ (bw q (+ (bw r b) (bw s c))) (bw p a))))
    (bw t (Rewrite<= add-comm (+ (bw p a) (bw q (+ (bw r b) (bw s c))))))
    (bw t (+ (bw p a) (bw q (+ (bw r b) (bw s c)))))
"
(* theorem add_assoc_1:
"bw t ((bw u ((bw p a) + (bw r b))) + (bw s c)) = 
 bw t ((bw p a) + (bw q ((bw r b) + (bw s c))))" (is "?lhs = ?rhs")
if "q >= t" and "u >= t"
proof -
    have         "?lhs = bw t (((bw p a) + (bw r b)) + (bw s c))"       using that(2) by (simp only: add_remove_prec)
    moreover have "... = bw t ((bw p a) + ((bw r b) + (bw s c)))"                     by (simp only: add.assoc)
    moreover have "... = bw t (((bw r b) + (bw s c)) + (bw p a))"                     by (simp only: add.commute)
    moreover have "... = bw t (bw q ((bw r b) + (bw s c)) + (bw p a))"  using that(1) by (simp only: add_remove_prec)
    moreover have "... = ?rhs" by (simp only: add.commute)
    ultimately show ?thesis by argo 
qed *)

syntax
    "_plus_prefix" :: "nat => nat => nat" ("+ _ _")
    "_geq_prefix" :: "nat => nat => nat" (">= _ _")
    "_leq_prefix" :: "nat => nat => nat" ("<= _ _")

translations
    "+ a b" \<rightleftharpoons> "a + b"
    ">= a b" \<rightleftharpoons> "a >= b"
    "<= a b" \<rightleftharpoons> "a <= b"

theorem add_assoc_1:
            "(bw t (+ (bw u (+ (bw p a) (bw r b))) (bw s c)))=(bw t (+ (bw p a) (bw q (+ (bw r b) (bw s c)))))" (is "?lhs = ?rhs")
            if "(>= q t)" and "(>= u t)"
            proof -
have          "?lhs = (bw t (+ (+ (bw p a) (bw r b)) (bw s c)))" using that by (simp only: add_remove_prec)
moreover have "... = (bw t (+ (bw p a) (+ (bw r b) (bw s c))))" using that by (simp only: add.assoc)
moreover have "... = (bw t (+ (+ (bw r b) (bw s c)) (bw p a)))" using that by (simp only: add.commute)
moreover have "... = (bw t (+ (bw q (+ (bw r b) (bw s c))) (bw p a)))" using that by (simp only: add_remove_prec)
moreover have "... = (bw t (+ (bw p a) (bw q (+ (bw r b) (bw s c)))))" using that by (simp only: add.commute)
ultimately show ?thesis by argo
qed

end

