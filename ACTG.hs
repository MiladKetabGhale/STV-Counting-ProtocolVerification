{--ACT Ginninderra 2012--}
module Candidates where
import Lib as L

filename :: String
filename = "ACTG1.txt"



-- to be put into a library later:

{- haskell lists to coq lists -} 
h2cl [] = Nil 
h2cl (a:as) = Cons a (h2cl as) 

{- Haskell Ints to Coq naturals -}
h2cn :: Int -> Nat
h2cn 0 = O
h2cn n = S (h2cn (n-1))


-- number of seats
st = h2cn 5


{--candidates--}  
data Cand =
  PAH
 |GIN
 |HEC
 |HIJ
 |COA
 |CHD
 |HAT
 |BUC
 |EZE
 |HUM
 |TAG
 |WAD
 |LEM
 |JBN
 |JAM
 |BEY
 |BOC
 |NAM
 |LEK
 |MCG
 |VAJ
 |POM
 |REK
 |THM
 |HNJ
 |BIM
 |WAM
 |DUV

{--list of all candidates--}
cand_all :: List Cand
cand_all =
 h2cl [PAH,GIN,HEC,HIJ,COA,CHD,HAT,BUC,EZE,HUM,TAG,WAD,LEM,JBN,JAM,BEY,BOC,NAM,LEK,MCG,VAJ,POM,REK,THM,HNJ,BIM,WAM,DUV]


cand_eq_dec :: Cand -> Cand -> Sumbool
cand_eq_dec c d =
    case c of {
   PAH ->
    case d of {
     PAH -> L.Left;
     _ -> L.Right};
   GIN ->
    case d of {
     GIN -> L.Left;
     _ -> L.Right};
   HEC ->
    case d of {
     HEC -> L.Left;
     _ -> L.Right};
   HIJ ->
    case d of {
     HIJ -> L.Left;
     _ -> L.Right};
   COA ->
    case d of {
     COA -> L.Left;
     _ -> L.Right};
   CHD ->
    case d of {
     CHD -> L.Left;
     _ -> L.Right};
   HAT ->
    case d of {
     HAT -> L.Left;
     _ -> L.Right};
   BUC ->
    case d of {
     BUC -> L.Left;
     _ -> L.Right};
   EZE ->
    case d of {
     EZE -> L.Left;
     _ -> L.Right};
   HUM ->
    case d of {
     HUM -> L.Left;
     _ -> L.Right};
   TAG ->
    case d of {
     TAG -> L.Left;
     _ -> L.Right};
   WAD ->
    case d of {
     WAD -> L.Left;
     _ -> L.Right};
   LEM ->
    case d of {
     LEM -> L.Left;
     _ -> L.Right};
   JBN ->
    case d of {
     JBN -> L.Left;
     _ -> L.Right};
   JAM ->
    case d of {
     JAM -> L.Left;
     _ -> L.Right};
   BEY ->
    case d of {
     BEY -> L.Left;
     _ -> L.Right};
   BOC ->
    case d of {
     BOC -> L.Left;
     _ -> L.Right};
   NAM ->
    case d of {
     NAM -> L.Left;
     _ -> L.Right};
   LEK ->
    case d of {
     LEK -> L.Left;
     _ -> L.Right};
   MCG ->
    case d of {
     MCG -> L.Left;
     _ -> L.Right};
   VAJ ->
    case d of {
     VAJ -> L.Left;
     _ -> L.Right};
   POM ->
    case d of {
     POM -> L.Left;
     _ -> L.Right};
   REK ->
    case d of {
     REK -> L.Left;
     _ -> L.Right};
   THM ->
    case d of {
     THM -> L.Left;
     _ -> L.Right};
   HNJ ->
    case d of {
     HNJ -> L.Left;
     _ -> L.Right};
   BIM ->
    case d of {
     BIM -> L.Left;
     _ -> L.Right};
   WAM ->
    case d of {
     WAM -> L.Left;
     _ -> L.Right};
   DUV ->
    case d of {
     DUV -> L.Left;
     _ -> L.Right}}
  
