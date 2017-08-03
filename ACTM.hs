{--ACT Molonglo 2012 --}
module ACTM where
import Lib as L

filename :: String
filename = "ACTM1.txt"



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
  RAS
 |KEA
 |LEC
 |SIA
 |JHT
 |GAK
 |BAA
 |COS
 |DRA
 |GAI
 |FIM
 |MAD
 |KUM
 |DIS
 |BOT
 |BIS
 |HAJ
 |DOS
 |LEE
 |JOG
 |MIJ
 |SET
 |GOM
 |CUM
 |CUD
 |POP
 

{--list of all candidates--}
cand_all :: List Cand
cand_all =
 h2cl [RAS,KEA,LEC,SIA,JHT,GAK,BAA,COS,DRA,GAI,FIM,MAD,KUM,DIS,BOT,BIS,HAJ,DOS,LEE,JOG,MIJ,SET,GOM,CUM,CUD,POP]

cand_eq_dec :: Cand -> Cand -> Sumbool
cand_eq_dec c d =
    case c of {
   RAS ->
    case d of {
     RAS -> L.Left;
     _ -> L.Right};
   KEA ->
    case d of {
     KEA -> L.Left;
     _ -> L.Right};
   LEC ->
    case d of {
     LEC -> L.Left;
     _ -> L.Right};
   SIA ->
    case d of {
     SIA -> L.Left;
     _ -> L.Right};
   JHT ->
    case d of {
     JHT -> L.Left;
     _ -> L.Right};
   GAK ->
    case d of {
     GAK -> L.Left;
     _ -> L.Right};
   BAA ->
    case d of {
     BAA -> L.Left;
     _ -> L.Right};
   COS ->
    case d of {
     COS -> L.Left;
     _ -> L.Right};
   DRA ->
    case d of {
     DRA -> L.Left;
     _ -> L.Right};
   GAI ->
    case d of {
     GAI -> L.Left;
     _ -> L.Right};
   FIM ->
    case d of {
     FIM -> L.Left;
     _ -> L.Right};
   MAD ->
    case d of {
     MAD -> L.Left;
     _ -> L.Right};
   KUM ->
    case d of {
     KUM -> L.Left;
     _ -> L.Right};
   DIS ->
    case d of {
     DIS -> L.Left;
     _ -> L.Right};
   BOT ->
    case d of {
     BOT -> L.Left;
     _ -> L.Right};
   BIS ->
    case d of {
     BIS -> L.Left;
     _ -> L.Right};
   HAJ ->
    case d of {
     HAJ -> L.Left;
     _ -> L.Right};
   DOS ->
    case d of {
     DOS -> L.Left;
     _ -> L.Right};
   LEE ->
    case d of {
     LEE -> L.Left;
     _ -> L.Right};
   JOG ->
    case d of {
     JOG -> L.Left;
     _ -> L.Right};
   MIJ ->
    case d of {
     MIJ -> L.Left;
     _ -> L.Right};
   SET ->
    case d of {
     SET -> L.Left;
     _ -> L.Right};
   GOM ->
    case d of {
     GOM -> L.Left;
     _ -> L.Right};
   CUM ->
    case d of {
     CUM -> L.Left;
     _ -> L.Right};
   CUD ->
    case d of {
     CUD -> L.Left;
     _ -> L.Right};
   POP ->
    case d of {
     POP -> L.Left;
     _ -> L.Right}}
  

     

