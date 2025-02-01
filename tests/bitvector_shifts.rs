use hello_world::check_equivalence;
mod common;

check_equiv_test!(
    shift,
    &["(>= u r)", "(> t s)", "(> t q)"],
    "(bw r (<< (bw u (<< (bw p a) (bw q b))) (bw s c)))",
    "(bw r (<< (bw p a) (bw t (+ (bw q b) (bw s c)))))"
);

check_equiv_test!(
    mul_by_two,
    &[],
    "(bw r (* (bw p a) 2))",
    "(bw r (<< (bw p a) 1))"
);

check_equiv_test!(
    left_shift_add_1,
    &["(>= u r)", "(>= s r)"],
    "(bw r (<< (bw s (+ (bw p a) (bw q b))) (bw t c)))",
    "(bw r (+ (bw u (<< (bw p a) (bw t c))) (bw u (<< (bw q b) (bw t c)))))"
);

check_equiv_test!(
    left_shift_add_2,
    &["(>= u r)", "(> s p)", "(> s q)"],
    "(bw r (<< (bw s (+ (bw p a) (bw q b))) (bw t c)))",
    "(bw r (+ (bw u (<< (bw p a) (bw t c))) (bw u (<< (bw q b) (bw t c)))))"
);

check_equiv_test!(
    left_shift_mult,
    &["(>= t r)", "(>= v r)"],
    "(bw r (<< (bw t (* (bw p a) (bw q b))) (bw u c)))",
    "(bw r (* (bw v (<< (bw p a) (bw u c))) (bw q b)))"
);

check_equiv_test!(
    merge_right_shift,
    &["(>= u p)", "(> t s)", "(> t q)"],
    "(bw r (>> (bw u (>> (bw p a) (bw q b))) (bw s c)))",
    "(bw r (>> (bw p a) (bw t (+ (bw q b) (bw s c)))))"
);

check_equiv_test!(
    shift_left_right,
    &["(>= t (+ p (^ 2 (- q 1))))"],
    "(>> (bw t (<< (bw p a) (bw q b))) (bw q b))",
    "(bw p a)"
);

check_equiv_test!(
    sum_same,
    &[],
    "(bw q (+ (bw p a) (bw p a)))",
    "(bw q (* (bw 2 2) (bw p a)))"
);

check_equiv_test!(
    add_right_shift,
    &[
        "(>= q t)",
        "(>= s (+ p (- (^ 2 u) 1)))",
        "(> v s)",
        "(> v t)",
    ],
    "(bw r (+ (bw p a) (bw q (>> (bw t b) (bw u c)))))",
    // "(bw p a)",
    "(bw r (>> (bw v (+ (bw s (<< (bw p a) (bw u c))) (bw t b))) (bw u c)))"
);
