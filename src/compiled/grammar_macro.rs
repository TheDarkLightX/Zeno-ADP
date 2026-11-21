/// Generate a single-track production schedule and optionally pair it with
/// a streaming algebra. See the compiler guide for supported layouts.
///
/// ```
/// use zeno_adp::{compiled_grammar, Operator};
/// use zeno_adp::algebras::Count;
///
/// #[derive(Clone)]
/// struct Segments(usize);
/// impl Operator for Segments {
///     fn arity(&self) -> usize { self.0 }
/// }
///
/// compiled_grammar! {
///     fn segments(input: char) -> Segments {
///         prefix |input, start, end|;
///         empty Empty => Ok(Some(Segments(0)));
///         extend Segment(split) => Ok((input[split] != ' ').then_some(Segments(1)));
///     }
///     with fn segment_count: Count = Count;
/// }
///
/// assert_eq!(segment_count(&['a', 'b', 'c']).unwrap().answer(), Some(&4));
/// ```
///
/// An unsupported layout or clause produces a compile-time diagnostic.
/// For example, a pivot clause needs the interval layout.
/// ```compile_fail
/// use zeno_adp::compiled_grammar;
/// use zeno_adp::Operator;
///
/// #[derive(Clone)]
/// struct Binary;
/// impl Operator for Binary {
///     fn arity(&self) -> usize { 2 }
/// }
///
/// compiled_grammar! {
///     fn bad(input: char) -> Binary {
///         prefix |input, start, end|;
///         pivot WrongLayout(split) => Ok(None);
///     }
/// }
/// ```
/// Pairing with `with fn` requires module scope or function-local items.
/// The compiler rejects pairing in an implementation, including when a
/// free function has the same name as the associated grammar.
///
/// ```compile_fail
/// use zeno_adp::{algebras::Count, compiled_grammar, Operator};
///
/// #[derive(Clone)]
/// struct Leaf;
/// impl Operator for Leaf {
///     fn arity(&self) -> usize { 0 }
/// }
///
/// compiled_grammar! {
///     fn parse(input: u8) -> Leaf {
///         prefix |tokens, start, end|;
///         empty Ambient => Ok(Some(Leaf));
///     }
/// }
///
/// struct Parser;
/// impl Parser {
///     compiled_grammar! {
///         fn parse(input: u8) -> Leaf {
///             prefix |tokens, start, end|;
///             empty Declared => Ok(None);
///         }
///         with fn count: Count = Count;
///     }
/// }
/// ```
///
/// The same restriction applies to trait implementations.
///
/// ```compile_fail
/// use zeno_adp::{algebras::Count, compiled, compiled_grammar, fast::Table, Error, Operator};
///
/// #[derive(Clone)]
/// struct Leaf;
/// impl Operator for Leaf {
///     fn arity(&self) -> usize { 0 }
/// }
///
/// compiled_grammar! {
///     fn parse(input: u8) -> Leaf {
///         prefix |tokens, start, end|;
///         empty Ambient => Ok(Some(Leaf));
///     }
/// }
///
/// struct Parser;
/// trait Parse {
///     fn parse(input: &[u8]) -> Result<impl compiled::Program<Op = Leaf> + '_, Error>;
///     fn count(input: &[u8]) -> Result<Table<u128>, Error>;
/// }
/// impl Parse for Parser {
///     compiled_grammar! {
///         fn parse(input: u8) -> Leaf {
///             prefix |tokens, start, end|;
///             empty Declared => Ok(None);
///         }
///         with fn count: Count = Count;
///     }
/// }
/// ```
#[macro_export]
macro_rules! compiled_grammar {
    (
        $vis:vis fn $name:ident($arg:ident: $token:ty) -> $op:ty {
            $layout:ident |$input:ident, $start:ident, $end:ident|;
            $($shape:ident $site:ident $(($split:ident))? => $body:expr;)+
        }
        $(with $eval_vis:vis fn $eval:ident: $fold:ty = $algebra:expr;)?
    ) => {
        $vis fn $name(bound_input: &[$token])
            -> ::core::result::Result<impl $crate::compiled::Program<Op = $op> + '_, $crate::Error>
        {
            {
                // Validate replay labels in a scope separate from caller expressions.
                #[allow(dead_code, non_camel_case_types)]
                enum ClauseNames { $($site,)+ }
            }
            $crate::compiled::generated::Generated::<$token, $op, _, {
                $crate::compiled_grammar!(@layout $name $layout)
            }>::bind(bound_input, $crate::compiled_grammar!(@clauses $layout
                (|$input: $token, $start, $end| -> $op)
                $($shape $site $(($split))? => $body;)+))
        }

        $(
            // Rust permits unnamed constants in modules and blocks, where
            // the paired function can name the grammar directly. It rejects
            // them in impls and traits, where that name could be ambiguous.
            const _: () = ();

            $eval_vis fn $eval(bound_input: &[$token]) -> ::core::result::Result<
                $crate::fast::Table<<$fold as $crate::fast::Fold<$op>>::Value>,
                $crate::Error,
            > {
                // Resolve the grammar before introducing the caller's argument name.
                let bind = $name;
                let $arg = bound_input;
                let _ = $arg;
                $crate::compiled::generated::tabulate::<_, $fold>($algebra, bind(bound_input))
            }
        )?
    };
    (@layout $name:ident prefix) => { true };
    (@layout $name:ident interval) => { false };
    (@layout $name:ident $other:ident) => {
        ::core::compile_error!(::core::concat!("unsupported layout ", ::core::stringify!($other),
            " in grammar ", ::core::stringify!($name), "; expected prefix or interval"))
    };
    (@clauses $layout:ident $scope:tt
        $($shape:ident $site:ident $(($split:ident))? => $body:expr;)+) => {
        $crate::compiled_grammar!(@group []
            $({ $crate::compiled_grammar!(@clause $layout $scope $shape $site $(($split))?; $body) })+)
    };
    // Reduce four consecutive groups per expansion to leave headroom under
    // rustc's default limit. Pairing only two at a time still takes n-1
    // expansions. Each tuple visits its left subtree before its right.
    (@group [$($groups:tt)*] $a:tt $b:tt $c:tt $d:tt $($rest:tt)*) => {
        $crate::compiled_grammar!(@group [$($groups)* (($a, $b), ($c, $d))] $($rest)*)
    };
    (@group [] $a:tt) => { $a };
    (@group [] $a:tt $b:tt) => { ($a, $b) };
    (@group [] $a:tt $b:tt $c:tt) => { (($a, $b), $c) };
    (@group [$($groups:tt)+] $($rest:tt)*) => {
        $crate::compiled_grammar!(@group [] $($groups)+ $($rest)*)
    };
    (@clause $layout:ident (|$input:ident: $token:ty, $start:ident, $end:ident| -> $op:ty)
        empty $site:ident; $body:expr) => {
        $crate::compiled::generated::Empty(::core::stringify!($site),
            |$input: &[$token], $start: ::core::primitive::usize, $end: ::core::primitive::usize|
                -> ::core::result::Result<::core::option::Option<$op>, $crate::Error> {
                let _ = ($input, $start, $end);
                $body
            })
    };
    (@clause prefix $scope:tt extend $site:ident($split:ident); $body:expr) => {
        $crate::compiled::generated::Extend(::core::stringify!($site),
            $crate::compiled_grammar!(@split $split $scope; $body))
    };
    (@clause interval $scope:tt pivot $site:ident($split:ident); $body:expr) => {
        $crate::compiled::generated::Pivot(::core::stringify!($site),
            $crate::compiled_grammar!(@split $split $scope; $body))
    };
    (@clause $layout:ident $scope:tt $shape:ident $site:ident $(($split:ident))?; $body:expr) => {
        ::core::compile_error!(::core::concat!("unsupported clause ", ::core::stringify!($site),
            " (", ::core::stringify!($shape), ") for ", ::core::stringify!($layout), " layout"))
    };
    (@split $split:ident (|$input:ident: $token:ty, $start:ident, $end:ident| -> $op:ty);
        $body:expr) => {
        |$input: &[$token], $start: ::core::primitive::usize, $end: ::core::primitive::usize,
            $split: ::core::primitive::usize|
            -> ::core::result::Result<::core::option::Option<$op>, $crate::Error> {
            let _ = ($input, $start, $end, $split);
            $body
        }
    };
}
