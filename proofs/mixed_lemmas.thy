theory mixed_lemmas
    imports rewrite_defs bitwise_lemmas
begin

lemma add_as_xor_and: "bw p a + bw q b = xor (bw p a) (bw q b) + 2 * (and (bw p a) (bw q b))"
for p q :: nat and a b c :: int
by (smt (verit) and.commute and.left_commute and.right_neutral and_eq_not_not_or bit.conj_disj_distrib 
    bit.conj_disj_distrib2 bit.conj_xor_distrib2 bit.xor_cancel_left bit.xor_def bit.xor_def2 bit.xor_one_left 
    bit.xor_one_right or.idem or_eq_not_not_and plus_and_or xor.assoc xor.right_neutral)

lemma xor_as_or_and: "xor (bw p a) (bw q b) = (or (bw p a) (bw q b)) - (and (bw p a) (bw q b))" 
by (smt (verit, ccfv_SIG) add_as_xor_and plus_and_or)

lemma neg_not: "-(bw p a) = (not (bw p a)) + 1" by (simp only: minus_eq_not_plus_1)

end