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
