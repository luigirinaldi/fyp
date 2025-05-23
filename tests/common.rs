#[macro_export]
macro_rules! check_equiv_test {
    ($name_str:ident, $preconditions:expr, $lhs:expr, $rhs:expr) => {
        #[test]
        fn $name_str() {
            let name = Some(concat!(file!(), '/', stringify!($name_str)));
            #[cfg(feature = "skip_isabelle")]
            $crate::check_equivalence(name, $preconditions, $lhs, $rhs, Some(true)).unwrap();
            #[cfg(not(feature = "skip_isabelle"))]
            $crate::check_equivalence(name, $preconditions, $lhs, $rhs, None).unwrap();
        }
    };
}
