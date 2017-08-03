{--ACT Molonglo 2008 --}
module Candidates where
import Lib as L

filename :: String
filename = "ACTMol.txt"



-- to be put into a library later:

{- haskell lists to coq lists -} 
h2cl [] = Nil 
h2cl (a:as) = Cons a (h2cl as) 

{- Haskell Ints to Coq naturals -}
h2cn :: Int -> Nat
h2cn 0 = O
h2cn n = S (h2cn (n-1))


-- number of seats
st = h2cn 7


{--candidates--}  
data Cand =
  WHC
 |BAB
 |PAF
 |SEZ
 |THP
 |LOL
 |BUJ
 |KEG
 |HAJ
 |FAT
 |TAK
 |TAG
 |CRH
 |ONB
 |ALJ
 |MUR
 |ROS
 |CUD
 |GES
 |EVK
 |LAA
 |SEA
 |VON
 |HOA
 |SAO
 |SCN
 |MCD
 |PID
 |RAS
 |LEC
 |KIE
 |HEM
 |COS
 |BAA
 |CRL
 |GAK
 |MAD
 |BAE
 |JOG
 |OND

{--list of all candidates--}
cand_all :: List Cand
cand_all =
 h2cl [WHC,BAB,PAF,SEZ,THP,LOL,BUJ,KEG,HAJ,FAT,TAK,TAG,CRH,ONB,ALJ,MUR,ROS,CUD,GES,EVK,LAA,SEA,VON,HOA,SAO,SCN,MCD,PID,RAS,LEC,KIE,HEM,COS,BAA,CRL,GAK,MAD,BAE,JOG,OND]

cand_eq_dec :: Cand -> Cand -> Sumbool
cand_eq_dec c d =
    case c of {
   BAB ->
    case d of {
     BAB -> L.Left;
     _ -> L.Right};
   WHC ->
    case d of {
     WHC -> L.Left;
     _ -> L.Right};
   PAF ->
    case d of {
     PAF -> L.Left;
     _ -> L.Right};
   SEZ ->
    case d of {
     SEZ -> L.Left;
     _ -> L.Right};
   THP ->
    case d of {
     THP -> L.Left;
     _ -> L.Right};
   LOL ->
    case d of {
     LOL -> L.Left;
     _ -> L.Right};
   BUJ ->
    case d of {
     BUJ -> L.Left;
     _ -> L.Right};
   KEG ->
    case d of {
     KEG -> L.Left;
     _ -> L.Right};
   HAJ ->
    case d of {
     HAJ -> L.Left;
     _ -> L.Right};
   FAT ->
    case d of {
     FAT -> L.Left;
     _ -> L.Right};
   TAK ->
    case d of {
     TAK -> L.Left;
     _ -> L.Right};
   TAG ->
    case d of {
     TAG -> L.Left;
     _ -> L.Right};
   CRH ->
    case d of {
     CRH -> L.Left;
     _ -> L.Right};
   ONB ->
    case d of {
     ONB -> L.Left;
     _ -> L.Right};
   ALJ ->
    case d of {
     ALJ -> L.Left;
     _ -> L.Right};
   MUR ->
    case d of {
     MUR -> L.Left;
     _ -> L.Right};
   ROS ->
    case d of {
     ROS -> L.Left;
     _ -> L.Right};
   CUD ->
    case d of {
     CUD -> L.Left;
     _ -> L.Right};
   GES ->
    case d of {
     GES -> L.Left;
     _ -> L.Right};
   EVK ->
    case d of {
     EVK -> L.Left;
     _ -> L.Right};
   LAA ->
    case d of {
     LAA -> L.Left;
     _ -> L.Right};
   SEA ->
    case d of {
     SEA -> L.Left;
     _ -> L.Right};
   VON ->
    case d of {
     VON -> L.Left;
     _ -> L.Right};
   HOA ->
    case d of {
     HOA -> L.Left;
     _ -> L.Right};
   SAO ->
    case d of {
     SAO -> L.Left;
     _ -> L.Right};
   SCN ->
    case d of {
     SCN -> L.Left;
     _ -> L.Right};
   MCD ->
    case d of {
     MCD -> L.Left;
     _ -> L.Right};
   PID ->
    case d of {
     PID -> L.Left;
     _ -> L.Right};
   RAS ->
    case d of {
     RAS -> L.Left;
     _ -> L.Right};
   LEC ->
    case d of {
     LEC -> L.Left;
     _ -> L.Right};
   KIE ->
    case d of {
     KIE -> L.Left;
     _ -> L.Right};
   HEM ->
    case d of {
     HEM -> L.Left;
     _ -> L.Right};
   COS ->
    case d of {
     COS -> L.Left;
     _ -> L.Right};
   BAA ->
    case d of {
     BAA -> L.Left;
     _ -> L.Right};
   CRL ->
    case d of {
     CRL -> L.Left;
     _ -> L.Right};
   GAK ->
    case d of {
     GAK -> L.Left;
     _ -> L.Right};
   BAE ->
    case d of {
     BAE -> L.Left;
     _ -> L.Right};
   MAD ->
    case d of {
     MAD -> L.Left;
     _ -> L.Right};
   JOG ->
    case d of {
     JOG -> L.Left;
     _ -> L.Right};
   OND ->
    case d of {
     OND -> L.Left;
     _ -> L.Right}}




     

