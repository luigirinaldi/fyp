use hello_world::check_equivalence;
mod common;

check_equiv_test!(
    commutativity_add,
    &[],
    "(bw r ( + (bw p a) (bw q b)))",
    "(bw r ( + (bw q b) (bw p a)))"
);

check_equiv_test!(
    commutativity_mult,
    &[],
    "(bw r ( * (bw p a) (bw q b)))",
    "(bw r ( * (bw q b) (bw p a)))"
);

check_equiv_test!(
    mult_assoc_1,
    &["(>= q t)", "(>= u t)"],
    "(bw t ( * (bw u (* (bw p a) (bw r b))) (bw s c)))",
    "(bw t ( * (bw p a) (bw q (* (bw r b) (bw s c)))))"
);

check_equiv_test!(
    mult_assoc_2,
    &["(>= q t)", "(<= (+ p r) u)"],
    "(bw t ( * (bw u (* (bw p a) (bw r b))) (bw s c)))",
    "(bw t ( * (bw p a) (bw q (* (bw r b) (bw s c)))))"
);

check_equiv_test!(
    mult_assoc_3,
    &["(<= (+ r s) q)", "(>= u t)"],
    "(bw t ( * (bw u (* (bw p a) (bw r b))) (bw s c)))",
    "(bw t ( * (bw p a) (bw q (* (bw r b) (bw s c)))))"
);

check_equiv_test!(
    mult_assoc_4,
    &["(<= (+ r s) q)", "(<= (+ p r) u)"],
    "(bw t ( * (bw u (* (bw p a) (bw r b))) (bw s c)))",
    "(bw t ( * (bw p a) (bw q (* (bw r b) (bw s c)))))"
);

check_equiv_test!(
    add_assoc_1,
    &["(>= q t)", "(>= u t)"],
    "(bw t ( + (bw u (+ (bw p a) (bw r b))) (bw s c)))",
    "(bw t ( + (bw p a) (bw q (+ (bw r b) (bw s c)))))"
);

check_equiv_test!(
    add_assoc_2,
    &["(< r q)", "(< s q)", "(>= u t)"],
    "(bw t ( + (bw u (+ (bw p a) (bw r b))) (bw s c)))",
    "(bw t ( + (bw p a) (bw q (+ (bw r b) (bw s c)))))"
);

check_equiv_test!(
    add_assoc_3,
    &["(>= q t)", "(< p u)", "(< r u)"],
    "(bw t ( + (bw u (+ (bw p a) (bw r b))) (bw s c)))",
    "(bw t ( + (bw p a) (bw q (+ (bw r b) (bw s c)))))"
);

check_equiv_test!(
    add_assoc_4,
    &["(< r q)", "(< s q)", "(< p u)", "(< r u)"],
    "(bw t ( + (bw u (+ (bw p a) (bw r b))) (bw s c)))",
    "(bw t ( + (bw p a) (bw q (+ (bw r b) (bw s c)))))"
);

check_equiv_test!(
    dist_over_add,
    &["(>= q r)", "(>= u r)", "(>= v r)"],
    "(bw r (* (bw p a) (+ (bw s b) (bw t c))))",
    "(bw r (+ (bw u (* (bw p a) (bw s b))) (bw v (* (bw p a) (bw t c)) ) ))"
);

check_equiv_test!(
    sum_same,
    &[],
    "(bw q (+ (bw p a) (bw p a)))",
    "(bw q (* (bw 2 2) (bw p a)))"
);

check_equiv_test!(
    mult_sum_same,
    &["(> t p)", "(> t 1)", "(>= s (+ p q))"],
    "(bw r (+ (bw s (* (bw p a) (bw q b))) (bw q b)))",
    "(bw r (* (bw t (+ (bw p a) (bw 1 1))) (bw q b)))"
);

check_equiv_test!(
    add_zero,
    &["(>= p p)"],
    "(bw p (+ (bw p a) (bw q 0)))",
    "(bw p a)"
);

check_equiv_test!(
    sub_to_neg,
    &[],
    "(bw r (- (bw p a) (bw q b)))",
    "(bw r (+ (bw p a) (- (bw q b))))"
);

check_equiv_test!(
    mul_one,
    &["(>= p p)"],
    "(bw p (* (bw p a) (bw q 1)))",
    "(bw p a)"
);
check_equiv_test!(
    mul_two,
    &[],
    "(bw r (* (bw p a) 2))",
    "(bw r (<< (bw p a) 1))"
);
