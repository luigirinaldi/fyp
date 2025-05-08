theory testproofs
    imports rewrite_lemmas
begin

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
theorem add_assoc_1:
"bw t ((bw u ((bw p a) + (bw r b))) + (bw s c)) = 
 bw t ((bw p a) + (bw q ((bw r b) + (bw s c))))" (is "?lhs = ?rhs")
if "q >= t" and "u >= t"
proof -
have "?lhs = bw t (((bw r b) + (bw s c)) + (bw p a))" 
    proof - 
    have "?lhs = bw t (((bw p a) + (bw r b)) + (bw s c))" using that(2) by (simp only: add_remove_prec)
    moreover have "... = bw t ((bw p a) + ((bw r b) + (bw s c)))" by (simp only: add.assoc)
    moreover have "... = bw t (((bw r b) + (bw s c)) + (bw p a))" by (simp only: add.commute)
    ultimately show ?thesis by argo
    qed
moreover have "?rhs = bw t (((bw r b) + (bw s c)) + (bw p a))"
    proof -
    have "?rhs = bw t (bw q ((bw r b) + (bw s c)) + (bw p a))" by (simp only: add.commute)
    then show ?thesis using that(1) by (simp only: add_remove_prec)
    qed
finally show ?thesis by argo 
qed
end

