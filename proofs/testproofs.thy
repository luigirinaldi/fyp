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
