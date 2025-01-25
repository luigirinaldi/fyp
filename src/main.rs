use hello_world::check_equivalence;

fn main() {
    let _ = check_equivalence(
        Some("shift"),
        &["(>= u r)", "(> t s)", "(> t q)"],
        "(bw r (<< (bw u (<< (bw p a) (bw q b))) (bw s c)))",
        "(bw r (<< (bw p a) (bw t (+ (bw q b) (bw s c)))))",
    );

    let _ = check_equivalence(
        Some("mul_by_two"),
        &[],
        "(bw r (* (bw p a) 2))",
        "(bw r (<< (bw p a) 1))",
    );

    let _ = check_equivalence(
        Some("left_shift_add_1"),
        &["(>= u r)", "(>= s r)"],
        "(bw r (<< (bw s (+ (bw p a) (bw q b))) (bw t c)))",
        "(bw r (+ (bw u (<< (bw p a) (bw t c))) (bw u (<< (bw q b) (bw t c)))))",
    );

    let _ = check_equivalence(
        Some("left_shift_add_2"),
        &["(>= u r)", "(> s p)", "(> s q)"],
        "(bw r (<< (bw s (+ (bw p a) (bw q b))) (bw t c)))",
        "(bw r (+ (bw u (<< (bw p a) (bw t c))) (bw u (<< (bw q b) (bw t c)))))",
    );

    let _ = check_equivalence(
        Some("left_shift_mult"),
        &["(>= t r)", "(>= v r)"],
        "(bw r (<< (bw t (* (bw p a) (bw q b))) (bw u c)))",
        "(bw r (* (bw v (<< (bw p a) (bw u c))) (bw q b)))",
    );

    // let _ = check_equivalence(
    //     Some("assoc-2"),
    //     &["(< p q)", "(< s q)"],
    //     "(bw r ( + (bw p a) (bw q (+ (bw p b) (bw s c)))))",
    //     "(bw r ( + (bw q (+ (bw p a) (bw p b))) (bw s c)))",
    // );

    // check_equivalence(
    //     Some("assoc-3"),
    //     &["(< p q)", "(< s q)", "(< r u)"],
    //     "(bw r ( + (bw p a) (bw u (+ (bw p b) (bw s c)))))",
    //     "(bw r ( + (bw q (+ (bw p a) (bw p b))) (bw s c)))",
    // );

    // check_equivalence(
    //     Some("multiply"),
    //     &["(< p q)", "(> k (+ p p))"],
    //     "(bw r (*
    //         (bw p a)
    //         (bw q (+ (bw p b) (bw p c)))))",
    //     "(bw r (+
    //         (bw k (* (bw p a) (bw p b)))
    //         (bw k (* (bw p a) (bw p c)))))",
    // );

    // check_equivalence(
    //     Some("multiply-2"),
    //     &["(< r q)", "(< r k)"],
    //     "(bw r (*
    //         (bw p a)
    //         (bw q (+ (bw p b) (bw p c)))))",
    //     "(bw r (+
    //         (bw k (* (bw p a) (bw p b)))
    //         (bw k (* (bw p a) (bw p c)))))",
    // );

    // check_equivalence(
    //     Some("multiply-3"),
    //     &["(< r t)", "(< r u)", "(< r v)"],
    //     "(bw r (*
    //         (bw p a)
    //         (bw t (+ (bw q b) (bw s c)))))",
    //     "(bw r (+
    //         (bw u (* (bw p a) (bw q b)))
    //         (bw v (* (bw p a) (bw s c)))))",
    // );

    // check_equivalence(
    //     Some("signed"),
    //     &["sign"],
    //     "(@ sign (bw b a))",
    //     "(- (* 2 (bw (- b 1) a)) (bw b a))",
    // );

    // check_equivalence(Some("test"), &["sign"], "(b)", "(+ 1 (- b 1))");

    // check_equivalence(
    //     Some("signed-1"),
    //     &["sign"],
    //     "(@ sign (bw b a))",
    //     "(- (bw b (* 2 a)) (bw b a))",
    // );

    // check_equivalence(
    //     Some("signed-2"),
    //     &["sign", "(>= p q)"],
    //     "(bw q (@ sign (bw p a)))",
    //     "(bw q a)",
    // );

    // // check_equivalence(
    // //     Some("signed-2a"),
    // //     &["sign", "(> q p)"],
    // //     "(bw q (@ sign (bw p a)))",
    // //     "(bw q a)",
    // // );

    // check_equivalence(
    //     Some("signed-4"),
    //     &["s"],
    //     "(+ (@ s (bw p a)) (bw p a))",
    //     "(bw p (* 2 a))",
    // );

    // check_equivalence(
    //     Some("sum"),
    //     &["(>= p q)"],
    //     "(bw q (+ (bw p a) (bw p a)))",
    //     "(bw q (* 2 a))",
    // );

    // // check_equivalence(
    // //     Some("signed-3"),
    // //     &["s"],
    // //     "(@ s (bw q (+ (@ s (bw p a)) (@ s (bw p b)))))",
    // //     //     "(-
    // //     //     (bw q (+
    // //     //         (* 4 (bw (- p 1) a))
    // //     //             ( + ( ~ (* 2 (bw p a))))
    // //     //                 (- (* 4 (bw (- p 1) b)) (* 2 (bw p b))
    // //     //         )
    // //     //     ))
    // //     //     (bw q (+ (- (* 2 (bw (- p 1) a)) (bw p a)) (- (* 2 (bw (- p 1) b)) (bw p b))))
    // //     // )",
    // //     "(@ s (bw q (+ (- (* 2 (bw (- p 1) a)) (bw p a)) (- (* 2 (bw (- p 1) b)) (bw p b)))))",
    // // )
    // // check_equivalence(
    // //     Some("signed-3"),
    // //     &["s"],
    // //     "(@ s (bw q (+ (@ s (bw p a)) (@ s (bw p b)))))",
    // //     "(-
    // //         (bw q (+
    // //             (* 4 (bw (- p 1) a))
    // //                 ( + ( ~ (* 2 (bw p a))))
    // //                     (- (* 4 (bw (- p 1) b)) (* 2 (bw p b))
    // //             )
    // //         ))
    // //         (bw q (+ (- (* 2 (bw (- p 1) a)) (bw p a)) (- (* 2 (bw (- p 1) b)) (bw p b))))
    // //     )",
    // //     // "(@ s (bw q (+ (- (* 2 (bw (- p 1) a)) (bw p a)) (- (* 2 (bw (- p 1) b)) (bw p b)))))",
    // // );

    // // check_equivalence(
    // //     Some("signed"),
    // //     &["sign"],
    // //     "(@ sign (bw p (+ a b)))",
    // //     "(@ sign (bw p (+ b a)))",
    // // );

    // // check_equivalence(
    // //     Some("signed-assoc"),
    // //     &["(< q (+ p 1))", "s"],
    // //     "(bw r ( + (@ s (bw p a)) (@ s (bw q (+ (@ s (bw p b)) (@ s (bw p c)))))))",
    // //     "(bw r ( + (@ s (bw p a)) (+ (bw q (+ (* 2 b) (* 2 c))) (bw q (+ b c)))))", // "(bw r ( + (@ s (bw q (+ (@ s (bw p a)) (@ s (bw p b))))) (@ s (bw p c))))",
    // // );
}
