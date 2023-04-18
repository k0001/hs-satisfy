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
  , DECIMAL
  ) --}
  where

import Data.Constraint
import Data.Singletons
import Data.Type.Bool
import Data.Type.Equality
import Data.Type.Ord
import Data.Void
import GHC.Real (Ratio((:%)))
import GHC.TypeLits qualified as L
import GHC.TypeLits.Singletons qualified as L
import KindInteger qualified as I
import KindRational (type (/), type (/=))
import KindRational qualified as R
import Prelude hiding (Ordering(..))
import Prelude as P
import Unsafe.Coerce (unsafeCoerce)

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
class PredicateCtx p k => Predicate p k where
  -- | The context necessary for 'satisfy' to make a decision.
  type PredicateCtx p k :: Constraint
  type PredicateCtx p k = ()
  -- | Term-level decision of whether scrutinee @s@ satisfies predicate @p@.
  --
  -- * If 'Left', then @'IsSatisfied' p s@ is 'False'. This is enforced by 'Satisfies'.
  --
  -- * If 'Right', then @'IsSatisfied' p s@ is 'True'. This is enforced by 'Unsatisfies'.
  satisfy
    :: forall (s :: k)
    .  Sing s
    -> Either (Unsatisfied p s) (Satisfied p s)

-- | If scrutinee @p@ satisfies predicate @p@, then this 'Constraint'
-- type-checks.
--
-- @'Satisfies' p s@ carries the corresponding 'PredicateCtx' and 'SatisfiesCtx'.
type Satisfies p (s :: k) =
  (PredicateCtx p k, IsSatisfied p s ~ 'True, SatisfiesCtx p s)

-- | If scrutinee @p@ does not satisfy predicate @p@, then this 'Constraint'
-- type-checks.
--
-- @'Unsatisfies' p s@ carries the corresponding 'PredicateCtx'.
type Unsatisfies p (s :: k) =
  (PredicateCtx p k, IsSatisfied p s ~ 'False)

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

{-
-- | All scrutiness satisfy the 'True' predicate.
instance Satisfy 'True s where
  type IsSatisfied 'True s = 'True

-- | All scrutiness satisfy the 'True' predicate.
instance Predicate 'True k where
  satisfy = Right . Satisfied
-}

--

-- | All scrutiness satisfy the @()@ predicate.
instance Satisfy () s where
  type IsSatisfied () s = 'True

-- | All scrutiness satisfy the @()@ predicate.
instance Predicate () k where
  satisfy = Right . Satisfied

--

{-
-- | No scrutiness satisfy the 'False' predicate.
instance Satisfy 'False s where
  type IsSatisfied 'False s = 'False

-- | No scrutiness satisfy the 'False' predicate.
instance Predicate 'False k where
  satisfy = Left . Unsatisfied
-}

--

-- | No scrutiness satisfy the 'Void' predicate.
instance Satisfy Void s where
  type IsSatisfied Void s = 'False

-- | No scrutiness satisfy the 'Void' predicate.
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
  type PredicateCtx (NOT p) k = Predicate p k
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
  type PredicateCtx (AND p q) k = (Predicate p k, Predicate q k)
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
  type PredicateCtx (OR p q) k = (Predicate p k, Predicate q k)
  satisfy (s :: Sing s) = case (satisfy @p s, satisfy @q s) of
    (Left  Unsatisfied{}, Left  Unsatisfied{}) -> Left (Unsatisfied s)
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
-- Notice that “equality” here refers to arithmetic equality as seen
-- in `Ord` or `Compare`, and not to propositional equality as seen
-- in `Refl`, `HRefl` or "Data.Singletons.Decide".
data EQ a
type role EQ nominal

instance (Predicate (EQ a) k, Satisfying (EQ a) s)
  => Satisfy (EQ (a :: k)) (s :: k) where
  type IsSatisfied (EQ a) s = OrdCond (Compare s a) 'False 'True 'False
  type SatisfiesCtx (EQ a) s = Compare s a ~ 'P.EQ

instance (Predicate (EQ a) I.Integer, Satisfying (EQ a) s)
  => Satisfy (EQ (a :: L.Natural)) (s :: I.Integer) where
  type IsSatisfied (EQ a) s = OrdCond (Compare s (I.P a)) 'False 'True 'False
  type SatisfiesCtx (EQ a) s = Compare s (I.P a) ~ 'P.EQ

instance (Predicate (EQ a) R.Rational, Satisfying (EQ a) s)
  => Satisfy (EQ (a :: L.Natural)) (s :: R.Rational) where
  type IsSatisfied (EQ a) s = OrdCond (Compare s (a / 1)) 'False 'True 'False
  type SatisfiesCtx (EQ a) s = Compare s (a / 1) ~ 'P.EQ

instance (Predicate (EQ a) L.Natural, Satisfying (EQ a) s)
  => Satisfy (EQ (a :: I.Integer)) (s :: L.Natural) where
  type IsSatisfied (EQ a) s = OrdCond (Compare (I.P s) a) 'False 'True 'False
  type SatisfiesCtx (EQ a) s = Compare (I.P s) a ~ 'P.EQ

instance (Predicate (EQ a) R.Rational, Satisfying (EQ a) s)
  => Satisfy (EQ (a :: I.Integer)) (s :: R.Rational) where
  type IsSatisfied (EQ a) s = OrdCond (Compare s (a / 1)) 'False 'True 'False
  type SatisfiesCtx (EQ a) s = Compare s (a / 1) ~ 'P.EQ

instance (Predicate (EQ a) L.Natural, Satisfying (EQ a) s)
  => Satisfy (EQ (a :: R.Rational)) (s :: L.Natural) where
  type IsSatisfied (EQ a) s = OrdCond (Compare (s / 1) a) 'False 'True 'False
  type SatisfiesCtx (EQ a) s = Compare (s / 1) a ~ 'P.EQ

instance (Predicate (EQ a) I.Integer, Satisfying (EQ a) s)
  => Satisfy (EQ (a :: R.Rational)) (s :: I.Integer) where
  type IsSatisfied (EQ a) s = OrdCond (Compare (s / 1) a) 'False 'True 'False
  type SatisfiesCtx (EQ a) s = Compare (s / 1) a ~ 'P.EQ

instance PredicateCtx (EQ a) L.Natural
  => Predicate (EQ (a :: L.Natural)) L.Natural where
  type PredicateCtx (EQ a) L.Natural = L.KnownNat a
  satisfy (s :: Sing s) = L.withKnownNat s $
    case L.cmpNat (Proxy @s) (Proxy @a) of
      LTI -> Left  (Unsatisfied s)
      EQI -> Right (Satisfied   s)
      GTI -> Left  (Unsatisfied s)

instance PredicateCtx (EQ a) I.Integer
  => Predicate (EQ (a :: L.Natural)) I.Integer where
  type PredicateCtx (EQ a) I.Integer = (L.KnownNat a, R.KnownRational (a/1))
  satisfy (s :: Sing s) = I.withKnownInteger s $
    case I.cmpInteger (Proxy @s) (Proxy @(I.P a)) of
      LTI -> Left  (Unsatisfied s)
      EQI -> Right (Satisfied   s)
      GTI -> Left  (Unsatisfied s)

instance PredicateCtx (EQ a) R.Rational
  => Predicate (EQ (a :: L.Natural)) R.Rational where
  type PredicateCtx (EQ a) R.Rational = R.KnownRational (a / 1)
  satisfy (s :: Sing s) = R.withKnownRational s $
    case R.cmpRational (Proxy @s) (Proxy @(a / 1)) of
      LTI -> Left  (Unsatisfied s)
      EQI -> Right (Satisfied   s)
      GTI -> Left  (Unsatisfied s)

instance PredicateCtx (EQ a) L.Natural
  => Predicate (EQ (a :: I.Integer)) L.Natural where
  type PredicateCtx (EQ a) L.Natural = I.KnownInteger a
  satisfy (s :: Sing s) = L.withKnownNat s $
    case I.cmpInteger (Proxy @(I.P s)) (Proxy @a) of
      LTI -> Left  (Unsatisfied s)
      EQI -> Right (Satisfied   s)
      GTI -> Left  (Unsatisfied s)

instance PredicateCtx (EQ a) I.Integer
  => Predicate (EQ (a :: I.Integer)) I.Integer where
  type PredicateCtx (EQ a) I.Integer = I.KnownInteger a
  satisfy (s :: Sing s) = I.withKnownInteger s $
    case I.cmpInteger (Proxy @s) (Proxy @a) of
      LTI -> Left  (Unsatisfied s)
      EQI -> Right (Satisfied   s)
      GTI -> Left  (Unsatisfied s)

instance PredicateCtx (EQ a) R.Rational
  => Predicate (EQ (a :: I.Integer)) R.Rational where
  type PredicateCtx (EQ a) R.Rational = R.KnownRational (a/1)
  satisfy (s :: Sing s) = R.withKnownRational s $
    case R.cmpRational (Proxy @s) (Proxy @(a / 1)) of
      LTI -> Left  (Unsatisfied s)
      EQI -> Right (Satisfied   s)
      GTI -> Left  (Unsatisfied s)

instance PredicateCtx (EQ a) L.Natural
  => Predicate (EQ (a :: R.Rational)) L.Natural where
  type PredicateCtx (EQ a) L.Natural = R.KnownRational a
  satisfy = \(s :: Sing s) ->
      case compare (toRational (fromSing s)) ra of
        P.LT -> case unsafeCoerce Refl :: Compare (s/1) a :~: 'P.LT of
          Refl -> Left (Unsatisfied s)
        P.EQ -> case unsafeCoerce Refl :: Compare (s/1) a :~: 'P.EQ of
          Refl -> Right (Satisfied s)
        P.GT -> case unsafeCoerce Refl :: Compare (s/1) a :~: 'P.GT of
          Refl -> Left (Unsatisfied s)
    where
      ra = R.toPrelude (R.fromSRational (R.rationalSing @a))

instance PredicateCtx (EQ a) I.Integer
  => Predicate (EQ (a :: R.Rational)) I.Integer where
  type PredicateCtx (EQ a) I.Integer = R.KnownRational a
  satisfy = \(s :: Sing s) ->
      case compare (toRational (I.toPrelude (I.fromSInteger s))) ra of
        P.LT -> case unsafeCoerce Refl :: Compare (s/1) a :~: 'P.LT of
          Refl -> Left (Unsatisfied s)
        P.EQ -> case unsafeCoerce Refl :: Compare (s/1) a :~: 'P.EQ of
          Refl -> Right (Satisfied s)
        P.GT -> case unsafeCoerce Refl :: Compare (s/1) a :~: 'P.GT of
          Refl -> Left (Unsatisfied s)
    where
      ra = R.toPrelude (R.fromSRational (R.rationalSing @a))

instance PredicateCtx (EQ a) R.Rational
  => Predicate (EQ (a :: R.Rational)) R.Rational where
  type PredicateCtx (EQ a) R.Rational = R.KnownRational a
  satisfy (s :: Sing s) = R.withKnownRational s $
    case R.cmpRational (Proxy @s) (Proxy @a) of
      LTI -> Left  (Unsatisfied s)
      EQI -> Right (Satisfied   s)
      GTI -> Left  (Unsatisfied s)

instance L.KnownChar a => Predicate (EQ a) Char where
  type PredicateCtx (EQ a) Char = L.KnownChar a
  satisfy (s :: Sing s) = L.withKnownChar s $
    case L.cmpChar (Proxy @s) (Proxy @a) of
      LTI -> Left  (Unsatisfied s)
      EQI -> Right (Satisfied   s)
      GTI -> Left  (Unsatisfied s)

instance L.KnownSymbol a => Predicate (EQ a) L.Symbol where
  type PredicateCtx (EQ a) L.Symbol = L.KnownSymbol a
  satisfy (s :: Sing s) = L.withKnownSymbol s $
    case L.cmpSymbol (Proxy @s) (Proxy @a) of
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

instance (Predicate (LT a) I.Integer, Satisfying (LT a) s)
  => Satisfy (LT (a :: L.Natural)) (s :: I.Integer) where
  type IsSatisfied (LT a) s = OrdCond (Compare s (I.P a)) 'True 'False 'False
  type SatisfiesCtx (LT a) s = Compare s (I.P a) ~ 'P.LT

instance (Predicate (LT a) R.Rational, Satisfying (LT a) s)
  => Satisfy (LT (a :: L.Natural)) (s :: R.Rational) where
  type IsSatisfied (LT a) s = OrdCond (Compare s (a / 1)) 'True 'False 'False
  type SatisfiesCtx (LT a) s = Compare s (a / 1) ~ 'P.LT

instance (Predicate (LT a) L.Natural, Satisfying (LT a) s)
  => Satisfy (LT (a :: I.Integer)) (s :: L.Natural) where
  type IsSatisfied (LT a) s = OrdCond (Compare (I.P s) a) 'True 'False 'False
  type SatisfiesCtx (LT a) s = Compare (I.P s) a ~ 'P.LT

instance (Predicate (LT a) R.Rational, Satisfying (LT a) s)
  => Satisfy (LT (a :: I.Integer)) (s :: R.Rational) where
  type IsSatisfied (LT a) s = OrdCond (Compare s (a / 1)) 'True 'False 'False
  type SatisfiesCtx (LT a) s = Compare s (a / 1) ~ 'P.LT

instance (Predicate (LT a) L.Natural, Satisfying (LT a) s)
  => Satisfy (LT (a :: R.Rational)) (s :: L.Natural) where
  type IsSatisfied (LT a) s = OrdCond (Compare (s / 1) a) 'True 'False 'False
  type SatisfiesCtx (LT a) s = Compare (s / 1) a ~ 'P.LT

instance (Predicate (LT a) I.Integer, Satisfying (LT a) s)
  => Satisfy (LT (a :: R.Rational)) (s :: I.Integer) where
  type IsSatisfied (LT a) s = OrdCond (Compare (s / 1) a) 'True 'False 'False
  type SatisfiesCtx (LT a) s = Compare (s / 1) a ~ 'P.LT

instance PredicateCtx (LT a) L.Natural
  => Predicate (LT (a :: L.Natural)) L.Natural where
  type PredicateCtx (LT a) L.Natural = L.KnownNat a
  satisfy (s :: Sing s) = L.withKnownNat s $
    case L.cmpNat (Proxy @s) (Proxy @a) of
      LTI -> Right (Satisfied   s)
      EQI -> Left  (Unsatisfied s)
      GTI -> Left  (Unsatisfied s)

instance PredicateCtx (LT a) I.Integer
  => Predicate (LT (a :: L.Natural)) I.Integer where
  type PredicateCtx (LT a) I.Integer = (L.KnownNat a, R.KnownRational (a/1))
  satisfy (s :: Sing s) = I.withKnownInteger s $
    case I.cmpInteger (Proxy @s) (Proxy @(I.P a)) of
      LTI -> Right (Satisfied   s)
      EQI -> Left  (Unsatisfied s)
      GTI -> Left  (Unsatisfied s)

instance PredicateCtx (LT a) R.Rational
  => Predicate (LT (a :: L.Natural)) R.Rational where
  type PredicateCtx (LT a) R.Rational = R.KnownRational (a / 1)
  satisfy (s :: Sing s) = R.withKnownRational s $
    case R.cmpRational (Proxy @s) (Proxy @(a / 1)) of
      LTI -> Right (Satisfied   s)
      EQI -> Left  (Unsatisfied s)
      GTI -> Left  (Unsatisfied s)

instance PredicateCtx (LT a) L.Natural
  => Predicate (LT (a :: I.Integer)) L.Natural where
  type PredicateCtx (LT a) L.Natural = I.KnownInteger a
  satisfy (s :: Sing s) = L.withKnownNat s $
    case I.cmpInteger (Proxy @(I.P s)) (Proxy @a) of
      LTI -> Right (Satisfied   s)
      EQI -> Left  (Unsatisfied s)
      GTI -> Left  (Unsatisfied s)

instance PredicateCtx (LT a) I.Integer
  => Predicate (LT (a :: I.Integer)) I.Integer where
  type PredicateCtx (LT a) I.Integer = I.KnownInteger a
  satisfy (s :: Sing s) = I.withKnownInteger s $
    case I.cmpInteger (Proxy @s) (Proxy @a) of
      LTI -> Right (Satisfied   s)
      EQI -> Left  (Unsatisfied s)
      GTI -> Left  (Unsatisfied s)

instance PredicateCtx (LT a) R.Rational
  => Predicate (LT (a :: I.Integer)) R.Rational where
  type PredicateCtx (LT a) R.Rational = R.KnownRational (a/1)
  satisfy (s :: Sing s) = R.withKnownRational s $
    case R.cmpRational (Proxy @s) (Proxy @(a / 1)) of
      LTI -> Right (Satisfied   s)
      EQI -> Left  (Unsatisfied s)
      GTI -> Left  (Unsatisfied s)

instance PredicateCtx (LT a) L.Natural
  => Predicate (LT (a :: R.Rational)) L.Natural where
  type PredicateCtx (LT a) L.Natural = R.KnownRational a
  satisfy = \(s :: Sing s) ->
      case compare (toRational (fromSing s)) ra of
        P.LT -> case unsafeCoerce Refl :: Compare (s/1) a :~: 'P.LT of
          Refl -> Right (Satisfied s)
        P.EQ -> case unsafeCoerce Refl :: Compare (s/1) a :~: 'P.EQ of
          Refl -> Left (Unsatisfied s)
        P.GT -> case unsafeCoerce Refl :: Compare (s/1) a :~: 'P.GT of
          Refl -> Left (Unsatisfied s)
    where
      ra = R.toPrelude (R.fromSRational (R.rationalSing @a))

instance PredicateCtx (LT a) I.Integer
  => Predicate (LT (a :: R.Rational)) I.Integer where
  type PredicateCtx (LT a) I.Integer = R.KnownRational a
  satisfy = \(s :: Sing s) ->
      case compare (toRational (I.toPrelude (I.fromSInteger s))) ra of
        P.LT -> case unsafeCoerce Refl :: Compare (s/1) a :~: 'P.LT of
          Refl -> Right (Satisfied s)
        P.EQ -> case unsafeCoerce Refl :: Compare (s/1) a :~: 'P.EQ of
          Refl -> Left (Unsatisfied s)
        P.GT -> case unsafeCoerce Refl :: Compare (s/1) a :~: 'P.GT of
          Refl -> Left (Unsatisfied s)
    where
      ra = R.toPrelude (R.fromSRational (R.rationalSing @a))

instance PredicateCtx (LT a) R.Rational
  => Predicate (LT (a :: R.Rational)) R.Rational where
  type PredicateCtx (LT a) R.Rational = R.KnownRational a
  satisfy (s :: Sing s) = R.withKnownRational s $
    case R.cmpRational (Proxy @s) (Proxy @a) of
      LTI -> Right (Satisfied   s)
      EQI -> Left  (Unsatisfied s)
      GTI -> Left  (Unsatisfied s)

instance L.KnownChar a => Predicate (LT a) Char where
  type PredicateCtx (LT a) Char = L.KnownChar a
  satisfy (s :: Sing s) = L.withKnownChar s $
    case L.cmpChar (Proxy @s) (Proxy @a) of
      LTI -> Right (Satisfied   s)
      EQI -> Left  (Unsatisfied s)
      GTI -> Left  (Unsatisfied s)

instance L.KnownSymbol a => Predicate (LT a) L.Symbol where
  type PredicateCtx (LT a) L.Symbol = L.KnownSymbol a
  satisfy (s :: Sing s) = L.withKnownSymbol s $
    case L.cmpSymbol (Proxy @s) (Proxy @a) of
      LTI -> Right (Satisfied   s)
      EQI -> Left  (Unsatisfied s)
      GTI -> Left  (Unsatisfied s)

--

-- | Scrutinee @s@ satisfies predicate @'LE' a@ when @s <= a@.
type LE a = EQ a `OR` LT a
-- | Scrutinee @s@ satisfies predicate @'GT' a@ when @s > a@.
type GT a = NOT (LE a)
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

instance forall a. PredicateCtx (FACTOR a) R.Rational
  => Predicate (FACTOR (a :: R.Rational)) R.Rational where
  type PredicateCtx (FACTOR a) R.Rational =
    (R.KnownRational a, a /= (0 / 1))
  satisfy (s :: Sing s)
    | _ :% 1 <- R.toPrelude (R.fromSRational s) / a -- '/' normalizes
    , Refl <- unsafeCoerce Refl :: R.Den (s / a) :~: 1 -- Meh.
    = Right (Satisfied s)
    | Refl <- unsafeCoerce Refl :: IsSatisfied (FACTOR a) s :~: 'False
    = Left (Unsatisfied s)
    where
      a = R.toPrelude (R.fromSRational (R.rationalSing @a))

instance (Predicate (FACTOR a) L.Natural, Satisfying (FACTOR a) s)
  => Satisfy (FACTOR (a :: L.Natural)) (s :: L.Natural) where
  type IsSatisfied (FACTOR a) s = IsSatisfied (EQ 0) (L.Mod s a)
  type SatisfiesCtx (FACTOR a) s = Satisfies (EQ 0) (L.Mod s a)

instance (Predicate (FACTOR a) I.Integer, Satisfying (FACTOR a) s)
  => Satisfy (FACTOR (a :: L.Natural)) (s :: I.Integer) where
  type IsSatisfied (FACTOR a) s = IsSatisfied (FACTOR (I.P a)) s
  type SatisfiesCtx (FACTOR a) s = Satisfies (FACTOR (I.P a)) s

instance (Predicate (FACTOR a) R.Rational, Satisfying (FACTOR a) s)
  => Satisfy (FACTOR (a :: L.Natural)) (s :: R.Rational) where
  type IsSatisfied (FACTOR a) s = IsSatisfied (FACTOR (a / 1)) s
  type SatisfiesCtx (FACTOR a) s = Satisfies (FACTOR (a / 1)) s

instance (Predicate (FACTOR a) L.Natural, Satisfying (FACTOR a) s)
  => Satisfy (FACTOR (a :: I.Integer)) (s :: L.Natural) where
  type IsSatisfied (FACTOR a) s = IsSatisfied (FACTOR a) (I.P s)
  type SatisfiesCtx (FACTOR a) s = Satisfies (FACTOR a) (I.P s)

instance (Predicate (FACTOR a) I.Integer, Satisfying (FACTOR a) s)
  => Satisfy (FACTOR (a :: I.Integer)) (s :: I.Integer) where
  type IsSatisfied (FACTOR a) s = IsSatisfied (EQ (I.P 0)) (I.Rem 'I.RoundDown s a)
  type SatisfiesCtx (FACTOR a) s = Satisfies (EQ (I.P 0)) (I.Rem 'I.RoundDown s a)

instance (Predicate (FACTOR a) R.Rational, Satisfying (FACTOR a) s)
  => Satisfy (FACTOR (a :: I.Integer)) (s :: R.Rational) where
  type IsSatisfied (FACTOR a) s = IsSatisfied (FACTOR (a / 1)) s
  type SatisfiesCtx (FACTOR a) s = Satisfies (FACTOR (a / 1)) s

instance (Predicate (FACTOR a) L.Natural, Satisfying (FACTOR a) s)
  => Satisfy (FACTOR (a :: R.Rational)) (s :: L.Natural) where
  type IsSatisfied (FACTOR a) s = IsSatisfied (FACTOR a) (s / 1)
  type SatisfiesCtx (FACTOR a) s = Satisfies (FACTOR a) (s / 1)

instance (Predicate (FACTOR a) I.Integer, Satisfying (FACTOR a) s)
  => Satisfy (FACTOR (a :: R.Rational)) (s :: I.Integer) where
  type IsSatisfied (FACTOR a) s = IsSatisfied (FACTOR a) (s / 1)
  type SatisfiesCtx (FACTOR a) s = Satisfies (FACTOR a) (s / 1)

instance (Predicate (FACTOR a) R.Rational, Satisfying (FACTOR a) s)
  => Satisfy (FACTOR (a :: R.Rational)) (s :: R.Rational) where
  type IsSatisfied (FACTOR a) s = IsSatisfied (EQ 1) (R.Den (s / a))
  type SatisfiesCtx (FACTOR a) s = Satisfies (EQ 1) (R.Den (s / a))

--------------------------------------------------------------------------------

-- | Whether the scrutinee can be represented exactly as a decimal number.
data DECIMAL

instance Predicate DECIMAL L.Natural where
  satisfy = Right . Satisfied

instance Predicate DECIMAL I.Integer where
  satisfy = Right . Satisfied

instance Predicate DECIMAL R.Rational where
  satisfy s = R.termination (Left (Unsatisfied s)) (Right (Satisfied s)) s

instance L.KnownNat s => Satisfy DECIMAL (s :: L.Natural) where
  type IsSatisfied DECIMAL s = 'True

instance I.KnownInteger s => Satisfy DECIMAL (s :: I.Integer) where
  type IsSatisfied DECIMAL s = 'True

instance Satisfying DECIMAL s => Satisfy DECIMAL (s :: R.Rational) where
  type IsSatisfied DECIMAL s = R.Terminates s
  type SatisfiesCtx DECIMAL s = R.Terminates s ~ 'True

