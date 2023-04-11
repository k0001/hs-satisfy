module Main (main) where

import Data.Singletons (sing)
import KindInteger (SInteger, P, N)
import KindRational (SRational)

import Satisfy qualified as S

--------------------------------------------------------------------------------

main :: IO ()
main = pure ()

-- 'S.EQ' relies on 'Compare', so this works.
_t1 :: S.Satisfied (S.EQ (P 0)) (N 0)
_t1 =  S.Satisfied sing

_t2 :: S.Satisfied (S.NOT (S.EQ (P 0))) (P 1)
_t2 =  S.Satisfied sing

