{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Satisfy {--}
  ( -- * Core
    Predicate(..)
  , Satisfy(..)
  , Satisfied(..)
  , Unsatisfied(..)
  , Satisfies
  , Unsatisfies
  , Satisfying
    -- * Boolean predicates
  , NOT
  , AND
  , OR
  , XOR
  , XNOR
  , IMPLIES
    -- * Ordering predicates
  , EQ
  , NE
  , LT
  , LE
  , GT
  , GE
    -- * Arithmethic predicates
  , FACTOR
  ) --}
  where

import Data.Constraint
import Data.Singletons
import Data.Type.Bool
import Data.Type.Equality
import Data.Type.Ord
import Data.Void
import GHC.TypeLits qualified as Lits
import KindInteger qualified as KI
import KindRational qualified as KR
import Prelude hiding (Ordering(..))
import Prelude as P

--------------------------------------------------------------------------------

-- | Proof that scrutinee @s@ is known to satisfy predicate @p@.
data Satisfied p s where
  Satisfied :: Satisfies p s => Sing s -> Satisfied p s

deriving stock instance Show (Sing s) => Show (Satisfied p s)
deriving stock instance Ord (Sing s) => Ord (Satisfied p s)
deriving stock instance Eq (Sing s) => Eq (Satisfied p s)

-- | Proof that scrutinee @s@ is known to not satisfy predicate @p@.
data Unsatisfied p s where
  Unsatisfied :: Unsatisfies p s => Sing s -> Unsatisfied p s

deriving stock instance Show (Sing s) => Show (Unsatisfied p s)
deriving stock instance Ord (Sing s) => Ord (Unsatisfied p s)
deriving stock instance Eq (Sing s) => Eq (Unsatisfied p s)

-- | A predicate @p@ for scrutinees of kind @k@.
class Predicate p k where
  -- | The context necessary for 'satisfy' to make a decision.
  type SatisfyCtx p (s :: k) :: Constraint
  type SatisfyCtx p s = ()
  -- | Term-level decision of whether scrutinee @s@ satisfies predicate @p@.
  --
  -- * If 'Left', then @'IsSatisfied' p s@ is 'False'. This is enforced by 'Satisfies'.
  --
  -- * If 'Right', then @'IsSatisfied' p s@ is 'True'. This is enforced by 'Unsatisfies'.
  satisfy
    :: forall (s :: k)
    .  SatisfyCtx p s
    => Sing s
    -> Either (Unsatisfied p s) (Satisfied p s)

-- | If scrutinee @p@ satisfies predicate @p@, then this 'Constraint'
-- type-checks.
--
-- @'Satisfies' p s@ carries the corresponding 'SatisfyCtx' and 'SatisfiesCtx'.
type Satisfies p s =
  (SatisfyCtx p s, IsSatisfied p s ~ 'True, SatisfiesCtx p s)

-- | If scrutinee @p@ does not satisfy predicate @p@, then this 'Constraint'
-- type-checks.
--
-- @'Unsatisfies' p s@ carries the corresponding 'SatisfyCtx'.
type Unsatisfies p s =
  (SatisfyCtx p s, IsSatisfied p s ~ 'False)

-- | @'Satisfying' p s@ type-checks if scrutinee @p@ is known to satisfiy
-- or not satisfy predicate @p@. It will resolve to @'Satisfies' p s@ or
-- @'Unsatisfies' p s@ accordingly.
type Satisfying p s =
  If (IsSatisfied p s) (Satisfies p s) (Unsatisfies p s)

-- | Type-level check that scrutinee @s@ satisfies predicate @p@.
--
-- Note that @p@ and @s@ can have different kinds.
class (Predicate p k, Satisfying p s) => Satisfy p (s :: k) where
  -- | If scrutinee @s@ satisfies predicate @p@, then @'Satisfies' p s@
  -- implies @'SatisfiesCtx' p s@.
  type SatisfiesCtx p s :: Constraint
  type SatisfiesCtx p s = ()
  -- | Whether scrutinee @s@ satisfies predicate @p@.
  --
  -- * If 'False', then @'satisfy' \@p (_ :: 'Sing' s)@ must be 'Left'.
  --
  -- * If 'True', then @'satisfy' \@p (_ :: 'Sing' s)@ must be 'Right'.
  type IsSatisfied p s :: Bool

--------------------------------------------------------------------------------

-- | All scrutiness satisfy the 'True' predicate.
instance Satisfy 'True s where
  type IsSatisfied 'True s = 'True

-- | All scrutiness satisfy the 'True' predicate.
instance Predicate 'True k where
  satisfy = Right . Satisfied

--

-- | Alternative spelling for the 'True' predicate.
instance Satisfy () s where
  type IsSatisfied () s = 'True

-- | Alternative spelling for the 'True' predicate.
instance Predicate () k where
  satisfy = Right . Satisfied

--

-- | No scrutiness satisfy the 'False' predicate.
instance Satisfy 'False s where
  type IsSatisfied 'False s = 'False

-- | No scrutiness satisfy the 'False' predicate.
instance Predicate 'False k where
  satisfy = Left . Unsatisfied

--

-- | Alternative spelling for the 'False' predicate.
instance Satisfy Void s where
  type IsSatisfied Void s = 'False

-- | Alternative spelling for the 'False' predicate.
instance Predicate Void k where
  satisfy = Left . Unsatisfied

--

-- | Scrutinee @s@ satisfies predicate @'NOT' p@ whenever scrutinee
-- @s@ does not satisfy predicate @p@.
data NOT p
type role NOT nominal

instance (Predicate p k, Satisfying (NOT p) s) => Satisfy (NOT p) (s :: k) where
  type IsSatisfied (NOT p) s = IsSatisfied p s == 'False
  type SatisfiesCtx (NOT p) s = Unsatisfies p s

instance forall p k. Predicate p k => Predicate (NOT p) k where
  type SatisfyCtx (NOT p) s = SatisfyCtx p s
  satisfy (s :: Sing s) = case satisfy @p s of
    Left  Unsatisfied{} -> Right (Satisfied   s)
    Right Satisfied  {} -> Left  (Unsatisfied s)

--

-- | Scrutinee @s@ satisfies predicate @p '`AND`' p@ whenever scrutinee
-- @s@ satisfies both predicates @p@ and @q@.
data p `AND` q
type role AND nominal nominal
infixl 7 `AND`

instance (Predicate p k, Predicate q k, Satisfying (AND p q) s)
  => Satisfy (AND p q) (s :: k) where
  type IsSatisfied (AND p q) s = IsSatisfied p s && IsSatisfied q s
  type SatisfiesCtx (AND p q) s = (Satisfies p s, Satisfies q s)

instance (Predicate p k, Predicate q k) => Predicate (AND p q) k where
  type SatisfyCtx (AND p q) s = (SatisfyCtx p s, SatisfyCtx q s)
  satisfy (s :: Sing s) = case (satisfy @p s, satisfy @q s) of
    (Left  Unsatisfied{}, Left  Unsatisfied{}) -> Left  (Unsatisfied s)
    (Left  Unsatisfied{}, Right Satisfied{}  ) -> Left  (Unsatisfied s)
    (Right Satisfied{}  , Left  Unsatisfied{}) -> Left  (Unsatisfied s)
    (Right Satisfied{}  , Right Satisfied{}  ) -> Right (Satisfied   s)

--

-- | Alternative spelling for the 'AND' predicate.
instance (Predicate p k, Predicate q k, Satisfying (p, q) s)
  => Satisfy (p, q) (s :: k) where
  type IsSatisfied (p, q) s = IsSatisfied p s && IsSatisfied q s
  type SatisfiesCtx (p, q) s = (Satisfies p s, Satisfies q s)

-- | Alternative spelling for the 'AND' predicate.
instance (Predicate p k, Predicate q k) => Predicate (p, q) k where
  type SatisfyCtx (p, q) s = SatisfyCtx (AND p q) s
  satisfy (s :: Sing s) = case (satisfy @p s, satisfy @q s) of
    (Left  Unsatisfied{}, Left  Unsatisfied{}) -> Left  (Unsatisfied s)
    (Left  Unsatisfied{}, Right Satisfied{}  ) -> Left  (Unsatisfied s)
    (Right Satisfied{}  , Left  Unsatisfied{}) -> Left  (Unsatisfied s)
    (Right Satisfied{}  , Right Satisfied{}  ) -> Right (Satisfied   s)

--

-- | Scrutinee @s@ satisfies predicate @p '`OR`' p@ whenever scrutinee
-- @s@ satisfies at least one of predicates @p@ and @q@.
data p `OR` q
type role OR nominal nominal
infixl 5 `OR`

instance (Predicate p k, Predicate q k, Satisfying (OR p q) s)
  => Satisfy (OR p q) (s :: k) where
  type IsSatisfied (OR p q) s = IsSatisfied p s || IsSatisfied q s
  type SatisfiesCtx (OR p q) s = (Satisfying p s, Satisfying q s)

instance (Predicate p k, Predicate q k) => Predicate (OR p q) k where
  type SatisfyCtx (OR p q) s = (SatisfyCtx p s, SatisfyCtx q s)
  satisfy (s :: Sing s) = case (satisfy @p s, satisfy @q s) of
    (Left  Unsatisfied{}, Left  Unsatisfied{}) -> Left (Unsatisfied s)
    (Left  Unsatisfied{}, Right Satisfied  {}) -> Right (Satisfied   s)
    (Right Satisfied  {}, Left  Unsatisfied{}) -> Right (Satisfied   s)
    (Right Satisfied  {}, Right Satisfied  {}) -> Right (Satisfied   s)

--

-- | Alternative spelling for the 'OR' predicate.
instance (Predicate p k, Predicate q k, Satisfying (Either p q) s)
  => Satisfy (Either p q) (s :: k) where
  type IsSatisfied (Either p q) s = IsSatisfied p s || IsSatisfied q s
  type SatisfiesCtx (Either p q) s = (Satisfying p s, Satisfying q s)

-- | Alternative spelling for the 'OR' predicate.
instance (Predicate p k, Predicate q k) => Predicate (Either p q) k where
  type SatisfyCtx (Either p q) s = (SatisfyCtx p s, SatisfyCtx q s)
  satisfy (s :: Sing s) = case (satisfy @p s, satisfy @q s) of
    (Left  Unsatisfied{}, Left  Unsatisfied{}) -> Left  (Unsatisfied s)
    (Left  Unsatisfied{}, Right Satisfied  {}) -> Right (Satisfied   s)
    (Right Satisfied  {}, Left  Unsatisfied{}) -> Right (Satisfied   s)
    (Right Satisfied  {}, Right Satisfied  {}) -> Right (Satisfied   s)

--

-- | Scrutinee @s@ satisfies @p '`IMPLIES`' p@ if scrutinee @s@
-- satisfying predicate @p@ implies scrutinee @s@ satisfying predicate @p@ .
type p `IMPLIES` q = NOT p `OR` q
infixr 4 `IMPLIES`

-- | Scrutinee @s@ satisfies predicate @p '`XOR`' p@ whenever scrutinee
-- @s@ satisfies only of predicates @p@ and @q@.
type p `XOR` q = (p `AND` NOT q) `OR` (NOT p `AND` q)
infixl 6 `XOR`

-- | Scrutinee @s@ satisfies predicate @p '`XNOR`' p@ whenever scrutinee
-- @s@ satisfies either both predicates @p@ and @q@, or none of them.
type p `XNOR` q = (p `AND` q) `OR` NOT (p `OR` q)
infixl 6 `XNOR`

--

-- | Scrutinee @s@ satisfies predicate @'EQ' a@ when @s == a@.
--
-- Notice that “equality” here refers to boolean equality as seen in
-- `Eq`, `Ord` or `Compare`, and not to propositional equality as seen
-- in `Refl`, `HRefl` or "Data.Singletons.Decide".
data EQ a
type role EQ nominal

instance (Predicate (EQ a) k, Satisfying (EQ a) s)
  => Satisfy (EQ (a :: k)) (s :: k) where
  type IsSatisfied (EQ a) s = OrdCond (Compare s a) 'False 'True 'False
  type SatisfiesCtx (EQ a) s = Compare s a ~ 'P.EQ

instance Predicate (EQ (a :: Lits.Natural)) Lits.Natural where
  type SatisfyCtx (EQ a) s = (Lits.KnownNat a, Lits.KnownNat s)
  satisfy (s :: Sing s) = case Lits.cmpNat (Proxy @s) (Proxy @a) of
    LTI -> Left  (Unsatisfied s)
    EQI -> Right (Satisfied   s)
    GTI -> Left  (Unsatisfied s)

instance Predicate (EQ (a :: Char)) Char where
  type SatisfyCtx (EQ a) s = (Lits.KnownChar a, Lits.KnownChar s)
  satisfy (s :: Sing s) = case Lits.cmpChar (Proxy @s) (Proxy @a) of
    LTI -> Left  (Unsatisfied s)
    EQI -> Right (Satisfied   s)
    GTI -> Left  (Unsatisfied s)

instance Predicate (EQ (a :: Lits.Symbol)) Lits.Symbol where
  type SatisfyCtx (EQ a) s = (Lits.KnownSymbol a, Lits.KnownSymbol s)
  satisfy (s :: Sing s) = case Lits.cmpSymbol (Proxy @s) (Proxy @a) of
    LTI -> Left  (Unsatisfied s)
    EQI -> Right (Satisfied   s)
    GTI -> Left  (Unsatisfied s)

instance Predicate (EQ (a :: KI.Integer)) KI.Integer where
  type SatisfyCtx (EQ a) s = (KI.KnownInteger a, KI.KnownInteger s)
  satisfy (s :: Sing s) = case KI.cmpInteger (Proxy @s) (Proxy @a) of
    LTI -> Left  (Unsatisfied s)
    EQI -> Right (Satisfied   s)
    GTI -> Left  (Unsatisfied s)

instance Predicate (EQ (a :: KR.Rational)) KR.Rational where
  type SatisfyCtx (EQ a) s = (KR.KnownRational a, KR.KnownRational s)
  satisfy (s :: Sing s) = case KR.cmpRational (Proxy @s) (Proxy @a) of
    LTI -> Left  (Unsatisfied s)
    EQI -> Right (Satisfied   s)
    GTI -> Left  (Unsatisfied s)

--

-- | Scrutinee @s@ satisfies predicate @'LT' a@ when @s < a@.
data LT a
type role LT nominal

instance (Predicate (LT a) k, Satisfying (LT a) s)
  => Satisfy (LT (a :: k)) (s :: k) where
  type IsSatisfied (LT a) s = OrdCond (Compare s a) 'True 'False 'False
  type SatisfiesCtx (LT a) s = Compare s a ~ 'P.LT

instance Predicate (LT (a :: Lits.Natural)) Lits.Natural where
  type SatisfyCtx (LT a) s = (Lits.KnownNat a, Lits.KnownNat s)
  satisfy (s :: Sing s) = case Lits.cmpNat (Proxy @s) (Proxy @a) of
    LTI -> Right (Satisfied   s)
    EQI -> Left  (Unsatisfied s)
    GTI -> Left  (Unsatisfied s)

instance Predicate (LT (a :: Char)) Char where
  type SatisfyCtx (LT a) s = (Lits.KnownChar a, Lits.KnownChar s)
  satisfy (s :: Sing s) = case Lits.cmpChar (Proxy @s) (Proxy @a) of
    LTI -> Right (Satisfied   s)
    EQI -> Left  (Unsatisfied s)
    GTI -> Left  (Unsatisfied s)

instance Predicate (LT (a :: Lits.Symbol)) Lits.Symbol where
  type SatisfyCtx (LT a) s = (Lits.KnownSymbol a, Lits.KnownSymbol s)
  satisfy (s :: Sing s) = case Lits.cmpSymbol (Proxy @s) (Proxy @a) of
    LTI -> Right (Satisfied   s)
    EQI -> Left  (Unsatisfied s)
    GTI -> Left  (Unsatisfied s)

instance Predicate (LT (a :: KI.Integer)) KI.Integer where
  type SatisfyCtx (LT a) s = (KI.KnownInteger a, KI.KnownInteger s)
  satisfy (s :: Sing s) = case KI.cmpInteger (Proxy @s) (Proxy @a) of
    LTI -> Right (Satisfied   s)
    EQI -> Left  (Unsatisfied s)
    GTI -> Left  (Unsatisfied s)

instance Predicate (LT (a :: KR.Rational)) KR.Rational where
  type SatisfyCtx (LT a) s = (KR.KnownRational a, KR.KnownRational s)
  satisfy (s :: Sing s) = case KR.cmpRational (Proxy @s) (Proxy @a) of
    LTI -> Right (Satisfied   s)
    EQI -> Left  (Unsatisfied s)
    GTI -> Left  (Unsatisfied s)

--

-- | Scrutinee @s@ satisfies predicate @'GT' a@ when @s > a@.
data GT a
type role GT nominal

instance (Predicate (GT a) k, Satisfying (GT a) s)
  => Satisfy (GT (a :: k)) (s :: k) where
  type IsSatisfied (GT a) s = OrdCond (Compare s a) 'False 'False 'True
  type SatisfiesCtx (GT a) s = Compare s a ~ 'P.GT

instance Predicate (GT (a :: Lits.Natural)) Lits.Natural where
  type SatisfyCtx (GT a) s = (Lits.KnownNat a, Lits.KnownNat s)
  satisfy (s :: Sing s) = case Lits.cmpNat (Proxy @s) (Proxy @a) of
    LTI -> Left  (Unsatisfied s)
    EQI -> Left  (Unsatisfied s)
    GTI -> Right (Satisfied   s)

instance Predicate (GT (a :: Char)) Char where
  type SatisfyCtx (GT a) s = (Lits.KnownChar a, Lits.KnownChar s)
  satisfy (s :: Sing s) = case Lits.cmpChar (Proxy @s) (Proxy @a) of
    LTI -> Left  (Unsatisfied s)
    EQI -> Left  (Unsatisfied s)
    GTI -> Right (Satisfied   s)

instance Predicate (GT (a :: Lits.Symbol)) Lits.Symbol where
  type SatisfyCtx (GT a) s = (Lits.KnownSymbol a, Lits.KnownSymbol s)
  satisfy (s :: Sing s) = case Lits.cmpSymbol (Proxy @s) (Proxy @a) of
    LTI -> Left  (Unsatisfied s)
    EQI -> Left  (Unsatisfied s)
    GTI -> Right (Satisfied   s)

instance Predicate (GT (a :: KI.Integer)) KI.Integer where
  type SatisfyCtx (GT a) s = (KI.KnownInteger a, KI.KnownInteger s)
  satisfy (s :: Sing s) = case KI.cmpInteger (Proxy @s) (Proxy @a) of
    LTI -> Left  (Unsatisfied s)
    EQI -> Left  (Unsatisfied s)
    GTI -> Right (Satisfied   s)

instance Predicate (GT (a :: KR.Rational)) KR.Rational where
  type SatisfyCtx (GT a) s = (KR.KnownRational a, KR.KnownRational s)
  satisfy (s :: Sing s) = case KR.cmpRational (Proxy @s) (Proxy @a) of
    LTI -> Left  (Unsatisfied s)
    EQI -> Left  (Unsatisfied s)
    GTI -> Right (Satisfied   s)

--

-- | Scrutinee @s@ satisfies predicate @'LE' a@ when @s <= a@.
type LE a = NOT (GT a)
-- | Scrutinee @s@ satisfies predicate @'GE' a@ when @s >= a@.
type GE a = NOT (LT a)
-- | Scrutinee @s@ satisfies predicate @'NE' a@ when @s /= a@.
type NE a = NOT (EQ a)

--

-- | Scrutinee @s@ satisfies predicate @'FACTOR' a@ when @a@ is a factor
-- of @s@. That is, when @a@ evenly divides @s@, which is the same as saying
-- that @s@ is a multiple of @a@.
data FACTOR a
type role FACTOR nominal

instance (Predicate (FACTOR a) Lits.Natural, Satisfying (FACTOR a) s)
  => Satisfy (FACTOR (a :: Lits.Natural)) (s :: Lits.Natural) where
  type IsSatisfied (FACTOR a) s = IsSatisfied (EQ 0) (Lits.Mod s a)
  type SatisfiesCtx (FACTOR a) s = Satisfies (EQ 0) (Lits.Mod s a)

instance (Predicate (FACTOR a) KI.Integer, Satisfying (FACTOR a) s)
  => Satisfy (FACTOR (a :: Lits.Natural)) (s :: KI.Integer) where
  type IsSatisfied (FACTOR a) s = IsSatisfied (FACTOR (KI.P a)) s
  type SatisfiesCtx (FACTOR a) s = Satisfies (FACTOR (KI.P a)) s

instance (Predicate (FACTOR a) KR.Rational, Satisfying (FACTOR a) s)
  => Satisfy (FACTOR (a :: Lits.Natural)) (s :: KR.Rational) where
  type IsSatisfied (FACTOR a) s = IsSatisfied (FACTOR (a KR./ 1)) s
  type SatisfiesCtx (FACTOR a) s = Satisfies (FACTOR (a KR./ 1)) s

instance (Predicate (FACTOR a) Lits.Natural, Satisfying (FACTOR a) s)
  => Satisfy (FACTOR (a :: KI.Integer)) (s :: Lits.Natural) where
  type IsSatisfied (FACTOR a) s = IsSatisfied (FACTOR a) (KI.P s)
  type SatisfiesCtx (FACTOR a) s = Satisfies (FACTOR a) (KI.P s)

instance (Predicate (FACTOR a) KI.Integer, Satisfying (FACTOR a) s)
  => Satisfy (FACTOR (a :: KI.Integer)) (s :: KI.Integer) where
  type IsSatisfied (FACTOR a) s = IsSatisfied (EQ (KI.P 0)) (KI.Rem 'KI.RoundDown s a)
  type SatisfiesCtx (FACTOR a) s = Satisfies (EQ (KI.P 0)) (KI.Rem 'KI.RoundDown s a)

instance (Predicate (FACTOR a) KR.Rational, Satisfying (FACTOR a) s)
  => Satisfy (FACTOR (a :: KI.Integer)) (s :: KR.Rational) where
  type IsSatisfied (FACTOR a) s = IsSatisfied (FACTOR (a KR./ 1)) s
  type SatisfiesCtx (FACTOR a) s = Satisfies (FACTOR (a KR./ 1)) s

instance (Predicate (FACTOR a) Lits.Natural, Satisfying (FACTOR a) s)
  => Satisfy (FACTOR (a :: KR.Rational)) (s :: Lits.Natural) where
  type IsSatisfied (FACTOR a) s = IsSatisfied (FACTOR a) (s KR./ 1)
  type SatisfiesCtx (FACTOR a) s = Satisfies (FACTOR a) (s KR./ 1)

instance (Predicate (FACTOR a) KI.Integer, Satisfying (FACTOR a) s)
  => Satisfy (FACTOR (a :: KR.Rational)) (s :: KI.Integer) where
  type IsSatisfied (FACTOR a) s = IsSatisfied (FACTOR a) (s KR./ 1)
  type SatisfiesCtx (FACTOR a) s = Satisfies (FACTOR a) (s KR./ 1)

instance (Predicate (FACTOR a) KR.Rational, Satisfying (FACTOR a) s)
  => Satisfy (FACTOR (a :: KR.Rational)) (s :: KR.Rational) where
  type IsSatisfied (FACTOR a) s = IsSatisfied (EQ 1) (KR.Den (s KR./ a))
  type SatisfiesCtx (FACTOR a) s = Satisfies (EQ 1) (KR.Den (s KR./ a))
