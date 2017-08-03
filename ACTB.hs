{--ACT Brindabella 2012--}
module ACTB where
import Lib as L

filename :: String
filename = "ACTB1.txt"



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
  GEM
 |DAJ
 |SEZ
 |WAA
 |MAK
 |GIM
 |JEV
 |COR
 |BUJ
 |KIM
 |MUB
 |BRA
 |ERM
 |DOB
 |JOK
 |PEC
 |LIM
 |HEA
 |LAN
 |SMB
 

{--list of all candidates--}
cand_all :: List Cand
cand_all =
 h2cl [GEM,DAJ,SEZ,WAA,MAK,GIM,JEV,COR,BUJ,KIM,MUB,BRA,ERM,DOB,JOK,PEC,LIM,HEA,LAN,SMB]


cand_eq_dec :: Cand -> Cand -> Sumbool
cand_eq_dec c d =
    case c of {
   GEM ->
    case d of {
     GEM -> L.Left;
     _ -> L.Right};
   DAJ ->
    case d of {
     DAJ -> L.Left;
     _ -> L.Right};
   SEZ ->
    case d of {
     SEZ -> L.Left;
     _ -> L.Right};
   WAA ->
    case d of {
     WAA -> L.Left;
     _ -> L.Right};
   MAK ->
    case d of {
     MAK -> L.Left;
     _ -> L.Right};
   GIM ->
    case d of {
     GIM -> L.Left;
     _ -> L.Right};
   JEV ->
    case d of {
     JEV -> L.Left;
     _ -> L.Right};
   COR ->
    case d of {
     COR -> L.Left;
     _ -> L.Right};
   BUJ ->
    case d of {
     BUJ -> L.Left;
     _ -> L.Right};
   KIM ->
    case d of {
     KIM -> L.Left;
     _ -> L.Right};
   MUB ->
    case d of {
     MUB -> L.Left;
     _ -> L.Right};
   BRA ->
    case d of {
     BRA -> L.Left;
     _ -> L.Right};
   ERM ->
    case d of {
     ERM -> L.Left;
     _ -> L.Right};
   DOB ->
    case d of {
     DOB -> L.Left;
     _ -> L.Right};
   JOK ->
    case d of {
     JOK -> L.Left;
     _ -> L.Right};
   PEC ->
    case d of {
     PEC -> L.Left;
     _ -> L.Right};
   LIM ->
    case d of {
     LIM -> L.Left;
     _ -> L.Right};
   HEA ->
    case d of {
     HEA -> L.Left;
     _ -> L.Right};
   LAN ->
    case d of {
     LAN -> L.Left;
     _ -> L.Right};
   SMB ->
    case d of {
     SMB -> L.Left;
     _ -> L.Right}}

