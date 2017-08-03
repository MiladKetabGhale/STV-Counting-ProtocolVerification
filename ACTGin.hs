{-- ACT Ginninderra 2008 --}
module ACTGin where
import Lib as L

filename :: String
filename = "ACTGin.txt"



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
  STJ
 |PED
 |BOC
 |POM
 |CIA
 |DUV
 |COA
 |MYJ
 |WAM
 |TOA
 |WHW
 |HAD
 |SIA
 |SEC
 |WAD
 |MIC
 |VEA
 |PAM
 |HIH
 |CHD
 |SMB
 |SAE
 |CRM
 |NIR
 |TUJ
 |HUM
 |HIJ

{--list of all candidates--}
cand_all :: List Cand
cand_all =
 h2cl [STJ,PED,BOC,POM,CIA,DUV,COA,MYJ,WAM,TOA,WHW,HAD,SIA,SEC,WAD,MIC,VEA,PAM,HIH,CHD,SMB,SAE,CRM,NIR,TUJ,HUM,HIJ]


cand_eq_dec :: Cand -> Cand -> Sumbool
cand_eq_dec c d =
    case c of {
   STJ ->
    case d of {
     STJ -> L.Left;
     _ -> L.Right};
   PED ->
    case d of {
     PED -> L.Left;
     _ -> L.Right};
   BOC ->
    case d of {
     BOC -> L.Left;
     _ -> L.Right};
   POM ->
    case d of {
     POM -> L.Left;
     _ -> L.Right};
   CIA ->
    case d of {
     CIA -> L.Left;
     _ -> L.Right};
   DUV ->
    case d of {
     DUV -> L.Left;
     _ -> L.Right};
   COA ->
    case d of {
     COA -> L.Left;
     _ -> L.Right};
   MYJ ->
    case d of {
     MYJ -> L.Left;
     _ -> L.Right};
   WAM ->
    case d of {
     WAM -> L.Left;
     _ -> L.Right};
   TOA ->
    case d of {
     TOA -> L.Left;
     _ -> L.Right};
   WHW ->
    case d of {
     WHW -> L.Left;
     _ -> L.Right};
   HAD ->
    case d of {
     HAD -> L.Left;
     _ -> L.Right};
   SIA ->
    case d of {
     SIA -> L.Left;
     _ -> L.Right};
   SEC ->
    case d of {
     SEC -> L.Left;
     _ -> L.Right};
   WAD ->
    case d of {
     WAD -> L.Left;
     _ -> L.Right};
   MIC ->
    case d of {
     MIC -> L.Left;
     _ -> L.Right};
   VEA ->
    case d of {
     VEA -> L.Left;
     _ -> L.Right};
   PAM ->
    case d of {
     PAM -> L.Left;
     _ -> L.Right};
   HIH ->
    case d of {
     HIH -> L.Left;
     _ -> L.Right};
   CHD ->
    case d of {
     CHD -> L.Left;
     _ -> L.Right};
   SMB ->
    case d of {
     SMB -> L.Left;
     _ -> L.Right};
   SAE ->
    case d of {
     SAE -> L.Left;
     _ -> L.Right};
   CRM ->
    case d of {
     CRM -> L.Left;
     _ -> L.Right};
   NIR ->
    case d of {
     NIR -> L.Left;
     _ -> L.Right};
   TUJ ->
    case d of {
     TUJ -> L.Left;
     _ -> L.Right};
   HUM ->
    case d of {
     HUM -> L.Left;
     _ -> L.Right};
   HIJ -> 
    case d of {
     HIJ -> L.Left;
     _ -> L.Right}}



