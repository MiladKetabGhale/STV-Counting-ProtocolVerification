{- to run elections with random ballots -}
module Candidates where
import Lib as L

filename :: String
filename = "random_election.txt"

-- to be put into a library later:

{- haskell lists to coq lists -} 
h2cl [] = Nil 
h2cl (a:as) = Cons a (h2cl as) 

{- Haskell Ints to Coq naturals -}
h2cn :: Int -> Nat
h2cn 0 = O
h2cn n = S (h2cn (n-1))

-- specific to the election example

{-- number of seats--}                     
st = h2cn 7

data Cand =
   A
 | B
 | C
 | D
 | E
 | F
 | G
 | H
 | I
 | J
 | K
 | L
 | M
 | N1
 | O0
 | P
 | Q0
 | R
 | S0
 | T2
 | A0
 | B0
 | C0
 | D0
 | E0
 | F0
 | G0
 | H0
 | I0
 | J0
 | K0
 | L0
 | M0
 | N10
 | O00
 | P0
 | Q00  deriving (Eq)

cand_all :: List Cand
cand_all =
  Cons A (Cons B (Cons C (Cons D (Cons E (Cons F (Cons G (Cons H (Cons I
    (Cons J (Cons K (Cons L (Cons M (Cons N1 (Cons O0 (Cons P (Cons Q0 (Cons
    R (Cons S0 (Cons T2 (Cons A0 (Cons B0 (Cons C0 (Cons D0 (Cons E0 (Cons F0 (Cons G0 (Cons H0 (Cons I0 (Cons J0 (Cons K0 (Cons L0 (Cons M0 (Cons N10 (Cons O00 (Cons P0 (Cons Q00 Nil))))))))))))))))))))))))))))))))))))


cand_eq_dec :: Cand -> Cand -> Sumbool
cand_eq_dec c d | c == d    = L.Left
                | otherwise = L.Right

