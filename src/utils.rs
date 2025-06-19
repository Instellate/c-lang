#[macro_export]
macro_rules! is_of_type {
    { $($ty:ident),* } => {
        $(
            ::paste::paste! {
                pub fn [<is_ $ty:snake>](&self) -> bool {
                    matches!(self, Self::$ty(_))
                }
            }
        )*
    };
}
