/// `Simplification` in
/// [Agda](https://hackage.haskell.org/package/Agda-2.6.0.1/docs/src/Agda.TypeChecking.Monad.Base.html#Simplification).
#[derive(Ord, PartialOrd, Eq, PartialEq, Copy, Clone, Debug, Hash)]
pub enum Simpl {
    Yes,
    No,
}

impl From<bool> for Simpl {
    fn from(b: bool) -> Self {
        if b {
            Simpl::Yes
        } else {
            Simpl::No
        }
    }
}

impl From<Simpl> for bool {
    fn from(v: Simpl) -> Self {
        match v {
            Simpl::Yes => true,
            Simpl::No => false,
        }
    }
}

impl Default for Simpl {
    fn default() -> Self {
        Simpl::No
    }
}

impl std::ops::Add for Simpl {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        match self {
            Simpl::Yes => Simpl::Yes,
            Simpl::No => rhs,
        }
    }
}
