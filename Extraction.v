Require Import Coq.Init.Peano.
Require Import Notations.
Require Import Coq.Lists.List.
Require Import Coq.Numbers.Natural.Peano.NPeano.
Require Import Coq.omega.Omega.
Require Import Coq.Arith.Le.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Numbers.NatInt.NZMul.
Require Import Coq.Structures.OrdersFacts.
Require Import Coq.ZArith.Znat. 
Require Import Coq.QArith.QArith_base.
Require Import  Coq.QArith.QOrderedType.
Require Import QArith_base Equalities Orders OrdersTac.
Require Import Coq.Sorting.Permutation.
Require Import Wf.
Require Import Lexicographic_Product.
Require Import Qreduction.
Require Import Coq.Bool.Bool.
Require Import Inverse_Image. 
Import ListNotations.
Require Import Union_STV.

Extraction Language Haskell.

Extraction "Lib.hs" hunion_count.
