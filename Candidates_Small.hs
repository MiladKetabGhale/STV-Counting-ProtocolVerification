{- to run the small election example -}
module Candidates where
import Lib as L

filename :: String
filename = "small_election.txt"

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
st = h2cn 2


data Cand =
  A
 |B
 |C

cand_all :: List Cand
cand_all = h2cl [A,B,C]


cand_eq_dec :: Cand -> Cand -> Sumbool
cand_eq_dec c d =
    case c of {
   A ->
    case d of {
     A -> L.Left;
     _ -> L.Right};
   B ->
    case d of {
     B -> L.Left;
     _ -> L.Right};
   C ->
    case d of {
     C -> L.Left;
     _ -> L.Right}}


