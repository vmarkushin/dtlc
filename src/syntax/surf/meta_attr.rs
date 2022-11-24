use crate::syntax::core::{display_application, pretty_list};
use crate::syntax::Ident;
use std::fmt::{Display, Formatter};
use vec1::Vec1;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MetaAttr {
    Ident(Ident),
    App(Ident, Vec1<MetaAttr>),
    Struct(Vec1<(Ident, String)>),
}

impl Display for MetaAttr {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "#(")?;
        match self {
            MetaAttr::Ident(ident) => {
                write!(f, "{}", ident)?;
            }
            MetaAttr::App(ident, args) => {
                display_application(f, ident, args)?;
            }
            MetaAttr::Struct(fields) => {
                write!(f, "{{")?;
                let fields = fields
                    .into_iter()
                    .map(|(field, value)| format!("{} = {}", field, value))
                    .collect::<Vec<_>>();
                pretty_list(f, &fields, ", ")?;
                write!(f, "}}")?;
            }
        }
        write!(f, ")")
    }
}
