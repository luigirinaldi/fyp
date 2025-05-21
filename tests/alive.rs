use hello_world::check_equivalence;
mod common;

check_equiv_test!(simple, &[], "(bw k (- k 1))", "(- k 1)");

check_equiv_test!(
    add_sub_1599_2,
    &[],
    "(bw k
        (- 
            (bw 1 (* 2 (>> (bw k x) (- k 1))))
            (bw 1 (>> (bw k x) (- k 1)))
        )
    )",
    "(ashr k (bw k x) (- k 1))"
);

check_equiv_test!(
    add_sub_1599_3,
    &[],
    "(bw k
        (- 
            (bw 1 (* 2 (>> (bw k x) (- k 1))))
            (bw 1 (>> (bw k x) (- k 1)))
        )
    )",
    "(bw k
        (- 
            (* 2 (bw 0 (>> (bw k x) (- k 1))))
            (bw 1 (>> (bw k x) (- k 1)))
        )
    )"
);

check_equiv_test!(
    add_sub_1599_4,
    &[],
    "(bw k
        (- 
            (0)
            (>> (bw k x) (- k 1))
        )
    )",
    "(bw k
        (- 
            (* 2 (bw 0 (>> (bw k x) (- k 1))))
            (bw (- k (- k 1)) (>> (bw k x) (- k 1)))
        )
    )"
);

check_equiv_test!(
    add_sub_1599,
    &["(>= 1 1)"],
    "(bw k (- 0 (>> (bw k x) (- k 1) )))",
    "(ashr k (bw k x) (- k 1))"
);

// check_equiv_test!(test_sign_extend, &[], "(sext 3 5 (-1))", "31");
