module NineDigits where

open import Data.Empty
open import Data.Bool using (Bool; true; false) 
open import Data.Nat renaming ( _?_ to _N?_ )
open import Data.Nat.Show
open import Data.Nat.Divisibility
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Fin using (Fin; toN; fromN; inject)
open import Data.Fin.Props renaming ( _?_ to _F?_)
open import Data.List renaming ([_] to L[_])
open import Data.Vec renaming (map to vmap)
open import Data.Product using (?; ?; _,_; proj1; proj2)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Unary using (Pred)
open import Data.String using (String; toCostring)
open import Data.Function

-- open import IO.Primitive
open import IO
import IO.Primitive as Prim
open import Foreign.Haskell
open import Data.Unit
import Data.Colist as Colist

_?_ : ? {P ?} › P › ¬ P › ?
_?_ = contradiction

occurs : ? {a n} › Decidable {a} _?_ › (x : a) › (ys : Vec a n) › Dec (x ? ys)
occurs _?_ _ [] = no ?()
occurs _?_ x (y ? ys) with x ? y
occurs _?_ x (.x ? ys)  | yes refl  = yes here
...                     | no x?y    with occurs _?_ x ys 
...                                 | yes x?ys  = yes (there x?ys)
...                                 | no  x?ys  = no  (notHereNorThere x?y x?ys)
                                         where notHereNorThere : ? {a n x y} {ys : Vec a n} › (¬ x ? y) › (¬ x ? ys) › (¬ x ? y ? ys)
                                               notHereNorThere {x = x} {y = .x} x?y x?ys here          = refl ? x?y
                                               notHereNorThere                  x?y x?ys (there x?ys)  = x?ys ? x?ys




data unique {a : Set} : {n : N} -> Pred (Vec a n) where
  empty : unique []
  uniq : ? {n x} {xs : Vec a n} -> (x?xs : ¬ x ? xs) -> (uxs : unique xs) -> unique (x ? xs)

¬unique : ? {a n} {x : a} {xs : Vec a n} › x ? xs › ¬ unique (x ? xs)
¬unique x?xs (uniq x?xs _) = x?xs ? x?xs

Digit : Set
Digit = Fin 9

digits : Vec Digit 9
digits = inject (fromN 0) ? inject (fromN 1) ? inject (fromN 2) ? inject (fromN 3) ? inject (fromN 4) ?
         inject (fromN 5) ? inject (fromN 6) ? inject (fromN 7) ? fromN 8 ? []

Digits : N › Set
Digits n = Vec Digit n

ds›N : ? {n} › Digits n › N
ds›N [] = 0
ds›N (d ? ds) = 10 * (ds›N ds) + (toN d + 1)

DivisableByLen : ? {n} › Pred (Digits n)
DivisableByLen {n} ds = n | (ds›N ds)

data GoodIntermediate : {n : N} › Pred (Digits n) where
  goodIntermediate : ? {n} {ds : Digits n} › (uds : unique ds) › DivisableByLen ds › GoodIntermediate ds
  
data GoodPrefix : {n : N} › Pred (Digits n) where
  empty : GoodPrefix []
  inherit : ? {n} {ds : Digits n} › (pds : GoodPrefix ds) › (d : Digit) › (id?ds : GoodIntermediate (d ? ds)) › GoodPrefix (d ? ds)

-- TODO: cleanup  
extend : ? {n} {ds : Digits n} {d : Digit} › GoodPrefix ds › (¬ d ? ds) › DivisableByLen (d ? ds) › GoodPrefix (d ? ds)
extend {.0} {.[]} {d} empty d?ds n+1|d?ds = inherit empty d (goodIntermediate (uniq d?ds empty) n+1|d?ds)
extend {suc n'} {d' ? ds'} {d}
  (inherit pds' .d' (goodIntermediate uds y))
  d?ds
  n+1|d?ds
  = inherit (inherit pds' d' (goodIntermediate uds y)) d (goodIntermediate (uniq d?ds uds) n+1|d?ds)
  
isGoodExtension : ? {n} {ds : Digits n} › GoodPrefix ds › (d : Digit) › Dec (GoodPrefix (d ? ds))
isGoodExtension {n} {ds} pds d with occurs _F?_ d ds
...                            | yes d?ds  = no ¬gp
                                 where ¬gp : ¬ GoodPrefix (d ? ds)
                                       ¬gp (inherit y .d (goodIntermediate uds n|ds)) = ¬unique d?ds uds
...                            | no  d?ds  with (suc n) |? (ds›N (d ? ds))
...                                        | yes n+1|d?ds  = yes (extend pds d?ds n+1|d?ds)
...                                        | no  n+1?d?ds = no ¬gp
                                             where ¬gp : ¬ GoodPrefix (d ? ds)
                                                   ¬gp (inherit y .d (goodIntermediate uds n+1|d?ds)) = n+1|d?ds ? n+1?d?ds


extensions : ? {n} {ds : Digits n} › GoodPrefix ds › List (? (? d › GoodPrefix (d ? ds)))
extensions {n} {ds} pds = gfilter tryExtend (toList digits)
  where tryExtend : (d : Digit) › Maybe (? (? d › GoodPrefix (d ? ds)))
        tryExtend d with isGoodExtension pds d
        ...         | yes pd?ds = just (d , pd?ds)
        ...         | no _      = nothing        

extendeds : ? {n} {ds : Digits n} › GoodPrefix ds › List (? (Digits (suc n)) (? ds' › GoodPrefix ds'))
extendeds {n} {ds} pds = map unpack (extensions pds)
  where unpack : ? (? d › GoodPrefix (d ? ds)) › ? (Digits (suc n)) (? ds' › GoodPrefix ds')
        unpack (d , pd?ds) = d ? ds , pd?ds

step : ? {n} › List (? (Digits n) (? ds › GoodPrefix ds)) › List (? (Digits (suc n)) (? ds' › GoodPrefix ds'))
step {n} pdss = concatMap extendedsUnpack pdss
  where extendedsUnpack : ? (Digits n) (? ds › GoodPrefix ds) › List (? (Digits (suc n)) (? ds' › GoodPrefix ds'))
        extendedsUnpack (ds , pds) = extendeds pds
        
showD : Digit › String
showD d = show (toN d)

showDs : ? {n} › Digits n › String
showDs ds = show (ds›N ds)

solution : List (? (Digits 9) (? ds › GoodPrefix ds))
solution = (step ° step ° step ° step ° step ° step ° step ° step ° step) (initial ? [])
  where initial : ? (Digits 0) (? ds › GoodPrefix ds)
        initial = [] , empty

test = map (showDs ° proj1) solution

main : Prim.IO ?
main = run (IO.mapM' putStrLn (Colist.fromList test))
