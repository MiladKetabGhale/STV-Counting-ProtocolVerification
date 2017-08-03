{-# LANGUAGE StandaloneDeriving, FlexibleInstances #-}
module Main where
{- imports automatically generated code for ANU_Union STV proof counting, -}
{- enables visualisation of proofs on screen and implements      -}
import Prelude as P
import Lib as L
import System.IO
import Data.List.Split as LS
import Candidates


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
                   ++ (show $ c2hl a0) 
                   ++ ";"++" " 
                   ++ (show (approx_frac . c2hQ .a1)) 
                   ++ ";"++ " " 
                   ++ (show (listBallot_listQ . c2hl. a2)) 
                   ++ ";" ++ " " 
                   ++ (show (c2hl b)) 
                   ++ ";" ++ " " 
                   ++ (show (c2hl c)) 
                   ++";" ++ " " 
                   ++  (show (c2hl d)) ++ ", " 
                   ++ "quota =" ++ " " ++ (show $ approx_frac . c2hQ $ e) 
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



