{-# LANGUAGE StandaloneDeriving, FlexibleInstances #-}
module Main where
{- imports automatically generated code for ANU_Union STV proof counting, -}
{- enables visualisation of proofs on screen and implements      -}
import Prelude as P
import Lib as L
import System.IO
import Data.List.Split as LS
import Candidates
--import ACTBri
--import ACTGin
--import ACTMol
--import ACTB
--import ACTG
--import ACTM
{--
import System.Random
import System.Random.Shuffle
import Control.Monad
import Control.Exception.Base
import Data.Array.ST
import Control.Monad.ST
import Data.STRef
--}


hTcl :: [a] -> List a
hTcl = foldl (\acc x -> Cons x acc) Nil


{- coq lists to haskell lists -}
c2hl :: List a -> [a]
c2hl Nil = []
c2hl (Cons x xs) = x : (c2hl xs)
 
{-- approximation up to three decimal digits of double numbers--}
approx_frac :: Double -> Double
approx_frac x = (fromIntegral (floor (x * t))) /t
 where t= 10 ^2

{- coq naturals to haskell Ints -}
c2hn :: Nat -> Int
c2hn O = 0
c2hn (S n) = (c2hn n) + 1

{--haskell pairs to Coq pairs--}
h2cProd :: (List cand, Q) -> Prod (List cand) Q
h2cProd ( l, p) = Pair l p

{--pair of list and rationals in Coq to haskell pair of list and double--}
prodC2h :: (Prod (List a) Q) -> ([a], Double)
prodC2h (Pair l b) = (c2hl l, approx_frac . c2hQ $ b)

listBallot_listQ :: [(Prod (List a) Q)] -> [ ([a],Double) ]
listBallot_listQ l = P.map prodC2h l

{--decimal to binary representation--}
dectoBin x = reverse $ decToBin' x
 where decToBin' 0 = []
       decToBin' y = let (a, b) = quotRem y 2 in [b] ++ decToBin' a

{--integers to Coq binary positive integers--}
h2cPos :: Integer  -> Positive
h2cPos n = (foldl (\acc x -> if x== 1 then XI acc else XO acc) XH) $ tail (dectoBin n)

{--haskell integers to Coq integers--}
h2cZ :: Integer -> Z
h2cZ n = if n P.== 0 then Z0 else if n P.< 0 then Zneg $ h2cPos (P.abs n) else Zpos $ h2cPos n 

h2cQ :: Integer -> Integer -> Q
h2cQ a b = Qmake (h2cZ a) (h2cPos b)

{--Coq positive integers to haskell integers--}
bintoDec :: Positive -> [Int]
bintoDec XH = [1]
bintoDec (XI p) = (bintoDec p) ++ [1]
bintoDec  (XO q) = (bintoDec q) ++ [0] 

pos_Int :: [Int] -> Integer
pos_Int l = if ((P.length l) == 0) then 0 else if ((P.length $ tail l) == 0) then ((toInteger (head l)) * 1) else ((toInteger (head l)) * (2 ^ (P.length $ tail l)) + (pos_Int $ tail l))

{--Coq integers to haskell integers--}
zToInt:: Z -> Integer
zToInt Z0 = 0
zToInt (Zneg p) = negate (pos_Int $ bintoDec p)
zToInt (Zpos q) = pos_Int $ bintoDec q

{--Coq rationals to haskell floats numbers--}
c2hQ (Qmake a b) = fromIntegral (zToInt a) / fromIntegral (pos_Int $ bintoDec b)


{- visualisation -}
instance(Show L.Bool) where 
 show (L.True) = "true"
 show (L.False) = "false"

deriving instance Show Cand

instance (Show b) => (Show (List b)) where
 show (Nil) = "Nil"
 show (Cons a p) = "(" ++ "Cons" ++ " " ++ (show a) ++ " "++ (show p) ++ ")"

instance (Show Positive)
 where 
      show (XH) = "XH"
      show (XO a) = "XO" ++ " " ++ (show a)
      show (XI a) = "XI" ++ " " ++ (show a)

instance (Show Z) where
      show (Z0) = "Z0"
      show (Zpos a) = "Zpos" ++ " "  ++ (show a)  
      show (Zneg a) = "Zneg" ++ " " ++ "(" ++ (show a) ++ ")" 

instance (Show Q) where 
      show (Qmake a b) = "(" ++ "("
                         ++ (show a) 
                         ++ ")" ++ " " ++ "(" 
                         ++ (show b) 
                         ++")" ++ ")"

instance (Show a) => (Show (Prod (List a) Q)) where
 show (Pair c b) = "(" ++ (show $ c2hl c) 
                   ++ "," 
                   ++ (show $ approx_frac . c2hQ $ b) ++ ")"

instance (Show a, Show b) => (Show (Prod a (Cand -> b))) where
 show (Pair d e) = (show d) ++ (show e)

instance (Show a, Show b) => (Show (Prod a (List b))) where
 show (Pair c d) = (show c) ++ (show $ c2hl d)

instance (Show a) => (Show (Prod () a)) where
 show (Pair _ c) = show c

instance (Show a, Show b) => Show (SigT a b) where
 show (ExistT x p) = (show p) ++ "\n" ++ (show x) 

instance Show (FT_Judgement Cand) where
   show(Winners l) = (P.take 60 (cycle "-")) 
                   ++ "\n" ++ "winners" ++ show (c2hl l) 
   show (State (Pair (Pair (Pair (Pair (Pair (Pair a0 a1) a2) b) c) d) e)) = (P.take 60 (cycle "-")) 
                   ++ "\n" 
                   ++ "state" ++ " " 
            --       ++ (show $ c2hl a0) 
            --       ++ ";"++" " 
                   ++ (show (approx_frac . c2hQ .a1)) 
                   ++ ";"++ " " 
            --       ++ (show (listBallot_listQ . c2hl. a2)) 
            --       ++ ";" ++ " " 
                   ++ (show (c2hl b)) 
                   ++ ";" ++ " " 
                   ++ (show (c2hl c)) 
                   ++";" ++ " " 
                   ++  (show (c2hl d)) ++ ", " 
           --        ++ "quota =" ++ " " ++ (show $ approx_frac . c2hQ $ e) 
   show (Initial l)= 
                  "initial::" ++ " " ++ "total ballots:=" 
                  ++ (show $ c2hn $ L.length l) 
                  ++ ", " ++ "formal ballots:=" ++ " " 
                  ++ (show $ (c2hn $ L.length $ L.filter cand_eq_dec l)) 
                  ++ ", " ++ "number of seats:=" ++ " " 
                  ++ (show $ c2hn st) 

instance (Show (Pf (FT_Judgement Cand))) where
         show (Ax a) = ""
         show (Mkp a j (p)) = show (p) ++ "\n" ++ show (j)

instance (Show a) => Show (Cand -> a) where
  show f = show_l (c2hl cand_all) where
    show_l [] = ""
    show_l [c] = (show c) ++ "{" ++ (show (f c)) ++ "}"
    show_l (c:cs) = (show c) ++ "{" ++ (show (f c)) ++ "} " ++ (show_l cs)


-- deriving instance (Eq Cand)
deriving instance (Read Cand)

{-- turning a list of cands into list of pairs of list of cands each of value one--}
fun_ballot :: [List cand] -> [(List cand, Q)]
fun_ballot l1 = P.zip l1 $ cycle [(Qmake (Zpos XH) XH)] 

{--a list of pairs of list of cands of value one to a list of Coq pairs of list cands of value one--}
fun_prod :: [(List cand,Q)] -> [Prod (List cand) Q]
fun_prod = P.map h2cProd 

hTcProd :: List cand -> Prod (List cand) Q
hTcProd l = Pair l (Qmake (Zpos XH) XH)


{--the main function computing results for the ballots in small_election.txt--}

main :: IO()
main= do
 c <- readFile filename
 print  $
        begin 
        $ h2cl ( P.map (hTcProd . (h2cl . (P.map (read :: String -> Cand)))) 
        $ P.map (splitOn "," ) $ lines c)   
             where
                  begin ba = hunion_count 
                             cand_all cand_eq_dec cand_in_dec st (Initial ba)



{--
main :: IO()
main= do
 c <- readFile filename
 print 
      $ begin
      $ hTcl 
      $ ((fun_prod . fun_ballot) 
      $ (P.map ( hTcl . P.reverse . (read:: String -> [Cand])) 
      $ lines c)) where
                   begin ba = hunion_count 
                              cand_all cand_eq_dec cand_in_dec st (Initial ba)
--}
{--checking if candidate c is in the list l--}
cand_in_dec :: Cand -> (List Cand) -> Sumbool
cand_in_dec c l =
  in_dec cand_eq_dec c l

in_dec :: (a1 -> a1 -> Sumbool) -> a1 -> (List a1) -> Sumbool
in_dec h a l =
  list_rect L.Right (\a0 l0 iHl ->
    let {s = h a0 a} in
    case s of {
     L.Left -> L.Left;
     L.Right -> iHl}) l

{--
-- number of seats
st = h2cn 5


{--candidates--}
data Cand =
  RAR
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
 h2cl [RAR,JEV,SIJ,MLB,BRA,GEM,SMB,RAG,RIB,DBB,DOB,SZS,PRS,ELS,MAT,SIW,HAJ,BUJ,MOD]

cand_eq_dec :: Cand -> Cand -> Sumbool
cand_eq_dec c d =
    case c of {
   RAR ->
    case d of {
     RAR -> L.Left;
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


{- haskell lists to coq lists -}
h2cl [] = Nil
h2cl (a:as) = Cons a (h2cl as)

{- Haskell Ints to Coq naturals -}
h2cn :: Int -> Nat
h2cn 0 = O
h2cn n = S (h2cn (n-1))
--}


{-- 
u = [A,B,C,D,E,F,G,H,I,J,K,L,M,N1,O0,P,Q0,R,S0,T2,A0,B0,C0,D0,E0,F0,H0,I0,J0,K0,L0,M0,N10,O00,P0,Q00]

main :: IO()
main= print $  initial_two $ hTcl $ ((fun_prod . fun_ballot) $ (L.map (\x -> h2cl x)) (vote_gen $ L.zip x y)) where 
 x = (copy_maker 320000 $  u )
 y= list_rand 320000

shuffle2 :: [a] -> StdGen -> ([a],StdGen)
shuffle2 xs gen = runST (do
        g <- newSTRef gen
        let randomRST lohi = do
              (a,s') <- liftM (randomR lohi) (readSTRef g)
              writeSTRef g s'
              return a
        ar <- newArray n xs
        xs' <- forM [1..n] $ \i -> do
                j <- randomRST (i,n)
                vi <- readArray ar i
                vj <- readArray ar j
                writeArray ar j vi
                return vj
        gen' <- readSTRef g
        return (xs',gen'))
  where
    n = L.length xs
    newArray :: Int -> [a] -> ST s (STArray s Int a)
    newArray n xs =  newListArray (1,n) xs

my_shuffle n = shuffle2 (u) (mkStdGen n)

copy_maker :: Int -> [Cand] -> [[Cand]]
copy_maker n l = l : (copy_maker  (n-1) l)

list_rand n m = P.take n $ randoms (mkStdGen m) :: [Int]

my_shuffle2 x = shuffle2 (P.fst x) (mkStdGen (P.snd x))

vote_gen l = P.map (P.fst . my_shuffle2) l

--}

{--
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
 | Q00

cand_all :: List Cand
cand_all =
  Cons A (Cons B (Cons C (Cons D (Cons E (Cons F (Cons G (Cons H (Cons I
    (Cons J (Cons K (Cons L (Cons M (Cons N1 (Cons O0 (Cons P (Cons Q0 (Cons
    R (Cons S0 (Cons T2 (Cons A0 (Cons B0 (Cons C0 (Cons D0 (Cons E0 (Cons F0 (Cons G0 (Cons H0 (Cons I0 (Cons J0 (Cons K0 (Cons L0 (Cons M0 (Cons N10 (Cons O00 (Cons P0 (Cons Q00 Nil))))))))))))))))))))))))))))))))))))


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
     _ -> L.Right};
   D ->
    case d of {
     D -> L.Left;
     _ -> L.Right};
   E ->
    case d of {
     E -> L.Left;
     _ -> L.Right};
   F ->
    case d of {
     F -> L.Left;
     _ -> L.Right};
   G ->
    case d of {
     G -> L.Left;
     _ -> L.Right};
   H ->
    case d of {
     H -> L.Left;
     _ -> L.Right};
    I ->
    case d of {
     I -> L.Left;
     _ -> L.Right};
   J ->
    case d of {
     J -> L.Left;
     _ -> L.Right};
   K ->
    case d of {
     K -> L.Left;
     _ -> L.Right};
   L ->
    case d of {
     L -> L.Left;
     _ -> L.Right};
   M ->
    case d of {
     M -> L.Left;
     _ -> L.Right};
   N1 ->
    case d of {
     N1 -> L.Left;
     _ -> L.Right};
   O0 ->
    case d of {
     O0 -> L.Left;
     _ -> L.Right};
   P ->
    case d of {
     P -> L.Left;
     _ -> L.Right};
   Q0 ->
    case d of {
     Q0 -> L.Left;
     _ -> L.Right};
    R ->
    case d of {
     R -> L.Left;
     _ -> L.Right};
   S0 ->
    case d of {
     S0 -> L.Left;
    _ -> L.Right};
   T2 ->
    case d of {
     T2 -> L.Left;
     _ -> L.Right};
   A0 ->
    case d of {
     A0 -> L.Left;
     _ -> L.Right};
   B0 ->
    case d of {
     B0 -> L.Left;
     _ -> L.Right};
   C0 ->
    case d of {
     C0 -> L.Left;
     _ -> L.Right};
   D0 ->
    case d of {
     D0 -> L.Left;
     _ -> L.Right};
    E0 ->
    case d of {
     E0 -> L.Left;
   F0 ->
    case d of {
     F0 -> L.Left;
     _ -> L.Right};
   G0 ->
    case d of {
     G0 -> L.Left;
     _ -> L.Right};
   H0 ->
    case d of {
     H0 -> L.Left;
     _ -> L.Right};
   I0 ->
    case d of {
     I0 -> L.Left;
     _ -> L.Right};
   J0 ->
    case d of {
     J0 -> L.Left;
     _ -> L.Right};
   K0 ->
    case d of {
     K0 -> L.Left;
     _ -> L.Right};
   L0 ->
    case d of {
     L0 -> L.Left;
     _ -> L.Right};
   M0 ->
    case d of {
     M0 -> L.Left;
     _ -> L.Right};
   N10 ->
    case d of {
     N10 -> L.Left;
     _ -> L.Right};
    O00 ->
    case d of {
     O00 -> L.Left;
     _ -> L.Right};
   P0 ->
    case d of {
     P0 -> L.Left;
     _ -> L.Right};
   Q00 ->
    case d of {
     Q00 -> L.Left;
     _ -> L.Right}}
  }
--}
