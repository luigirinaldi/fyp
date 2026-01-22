theory bitwise_lemmas
    imports rewrite_defs arith_lemmas
begin

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

lemma and_assoc: "(and (and a b) c) = (and a (and b c))" by (simp only: and.assoc)
lemma or_assoc: "(or (or a b) c) = (or a (or b c))" by (simp only: or.assoc)
lemma not_bw_not: "bw p (not (bw p (not (bw p a)))) = (bw p a)" if "p>0" by (metis bit.double_compl bw_def take_bit_int_def take_bit_not_take_bit)

lemma and_distrib: "and a (or b c) = or (and a b) (and a c)" for a b c :: int by (simp only: Bit_Operations.ring_bit_operations_class.bit.conj_disj_distrib and.commute)

lemma xor_and_or_help: "and (or a b) (or (not a) (not b)) = xor a b" for a b :: int by (simp add: bit.xor_def2)

lemma xor_and_or: "and (or (bw p a) (bw p b)) (or (bw p (not (bw p a))) (bw p (not (bw p b)))) = xor (bw p a) (bw p b)" for a b :: int 
using xor_and_or_help by (metis bw_def take_bit_and take_bit_eq_mod take_bit_not_take_bit take_bit_or take_bit_xor)

lemma and_self: "and a a = a" by simp
lemma or_self: "or a a = a" by simp
lemma and_not_self: "(and (bw p a) (bw p (not (bw p a)))) = 0" by (metis bit.xor_self or_self xor_and_or)
lemma or_not_self: "(or (bw p a) (bw p (not (bw p a)))) = bw p (-1)" by (metis bit.disj_cancel_right bw_def take_bit_eq_mod take_bit_not_take_bit take_bit_or)

lemma "bw q (or (bw p a) (bw r b)) = or (bw p a) (bw r b)" if "q \<ge> p" and "q >= r"
by (metis bw_def reduce_mod take_bit_eq_mod take_bit_or that) 

end