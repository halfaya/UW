module Integer where

open import Data.Bool
open import Data.Nat as ℕ
  using (ℕ) renaming (_+_ to _ℕ+_; _*_ to _ℕ*_)
open import Data.Integer
  renaming (_+_ to _ℤ+_; _*_ to _ℤ*_)

infixl 6 _+_
--infixl 7 _*_

record Z : Set where
  constructor [_,_]
  field
    sgn : Bool -- false is negative; true is positive
    abs : ℕ

-- two zeros map to a single zero
Z→ℤ : Z → ℤ
Z→ℤ [ false , ℕ.zero ]    = + ℕ.zero
Z→ℤ [ false , ℕ.suc abs ] = -[1+ abs ]
Z→ℤ [ true  , abs ]       = + abs

-- zero maps to the positive zero
ℤ→Z : ℤ → Z
ℤ→Z (+_ n)     = [ true , n ]
ℤ→Z (-[1+_] n) = [ false , ℕ.suc n ]

_+_ : Z → Z → Z
 [  false , ma ]       + [ false , na ]       = [ false , ma ℕ+ na ]
 [  false , ℕ.zero ]   + [ true , na ]        = [ true , na ]
 [  false , ℕ.suc ma ] + [ true , ℕ.zero ]    = [ false , ℕ.suc ma ]
 [  false , ℕ.suc ma ] + [ true , ℕ.suc na ]  = [ false , ma ] + [ true , na ]
 [  true , ℕ.zero ]    + [ false , na ]       = [ false , na ]
 [  true , ℕ.suc ma ]  + [ false , ℕ.zero ]   = [ true , ℕ.suc ma ]
 [  true , ℕ.suc ma ]  + [ false , ℕ.suc na ] = [ true , ma ] + [ false , na ]
 [  true  , ma ]       + [ true  , na ]       = [ true , ma ℕ+ na ]


