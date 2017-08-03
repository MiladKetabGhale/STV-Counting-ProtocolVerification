{--ACT Brindabella 2008 --}
module ACTBri where
import Lib as L

filename :: String
filename = "ACTBri.txt"



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
  RAA
 |JEV
 |SIJ
 |MLB
 |BRA
 |GEM
 |SMB
 |RAG
 |RIB
 |DBB
 |DOB
 |SZS
 |PRS
 |ELS
 |MAT
 |SIW
 |HAJ
 |BUJ
 |MOD

 

{--list of all candidates--}
cand_all :: List Cand
cand_all =
 h2cl [RAA,JEV,SIJ,MLB,BRA,GEM,SMB,RAG,RIB,DBB,DOB,SZS,PRS,ELS,MAT,SIW,HAJ,BUJ,MOD]

cand_eq_dec :: Cand -> Cand -> Sumbool
cand_eq_dec c d =
    case c of {
   RAA ->
    case d of {
     RAA -> L.Left;
     _ -> L.Right};
   JEV ->
    case d of {
     JEV -> L.Left;
     _ -> L.Right};
   SIJ ->
    case d of {
     SIJ -> L.Left;
     _ -> L.Right};
   MLB ->
    case d of {
     MLB -> L.Left;
     _ -> L.Right};
   BRA ->
    case d of {
     BRA -> L.Left;
     _ -> L.Right};
   GEM ->
    case d of {
     GEM -> L.Left;
     _ -> L.Right};
   SMB ->
    case d of {
     SMB -> L.Left;
     _ -> L.Right};
   RAG ->
    case d of {
     RAG -> L.Left;
     _ -> L.Right};
   RIB ->
    case d of {
     RIB -> L.Left;
     _ -> L.Right};
   DBB ->
    case d of {
     DBB -> L.Left;
     _ -> L.Right};
   DOB ->
    case d of {
     DOB -> L.Left;
     _ -> L.Right};
   SZS ->
    case d of {
     SZS -> L.Left;
     _ -> L.Right};
   PRS ->
    case d of {
     PRS -> L.Left;
     _ -> L.Right};
   ELS ->
    case d of {
     ELS -> L.Left;
     _ -> L.Right};
   MAT ->
    case d of {
     MAT -> L.Left;
     _ -> L.Right};
   SIW ->
    case d of {
     SIW -> L.Left;
     _ -> L.Right};
   HAJ ->
    case d of {
     HAJ -> L.Left;
     _ -> L.Right};
   BUJ ->
    case d of {
     BUJ -> L.Left;
     _ -> L.Right};
   MOD ->
    case d of {
     MOD -> L.Left;
     _ -> L.Right}}
     

