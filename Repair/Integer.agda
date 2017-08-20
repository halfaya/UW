module Integer where

open import Data.Bool
open import Data.Nat as ℕ
  using (ℕ) renaming (_+_ to _ℕ+_; _*_ to _ℕ*_)
open import Data.Nat.Properties.Simple
open import Data.Integer
  renaming (_+_ to _ℤ+_; _*_ to _ℤ*_)
open import Relation.Binary.PropositionalEquality
open import Function

infixl 6 _+_ _⊕_

record Z : Set where
  constructor [_,_]
  field
    sgn : Bool -- false is negative; true is positive
    abs : ℕ

-- canonical form for Z
cf : Z → Z
cf [ false , ℕ.zero ]    = [ true  , ℕ.zero ]
cf [ false , ℕ.suc abs ] = [ false , ℕ.suc abs ]
cf [ true  , abs ]       = [ true  , abs ]

-- equivalence of canonical forms

infix 4 _≡cf_

_≡cf_ : Z → Z → Set
m ≡cf n = (cf m) ≡ (cf n)

cf-refl : {n : Z} → n ≡cf n
cf-refl = refl

cf-sym : {m n : Z} → m ≡cf n → n ≡cf m
cf-sym {[ false , ℕ.zero ]} {[ false , ℕ.zero ]} refl = refl
cf-sym {[ false , ℕ.zero ]} {[ false , ℕ.suc abs' ]} ()
cf-sym {[ false , ℕ.suc abs ]} {[ false , ℕ.zero ]} ()
cf-sym {[ false , ℕ.suc abs ]} {[ false , ℕ.suc .abs ]} refl = refl
cf-sym {[ false , ℕ.zero ]} {[ true , ℕ.zero ]} refl = refl
cf-sym {[ false , ℕ.zero ]} {[ true , ℕ.suc abs' ]} ()
cf-sym {[ false , ℕ.suc abs ]} {[ true , ℕ.zero ]} ()
cf-sym {[ false , ℕ.suc abs ]} {[ true , ℕ.suc abs' ]} ()
cf-sym {[ true , ℕ.zero ]} {[ false , ℕ.zero ]} refl = refl
cf-sym {[ true , ℕ.zero ]} {[ false , ℕ.suc abs' ]} ()
cf-sym {[ true , ℕ.suc abs ]} {[ false , ℕ.zero ]} ()
cf-sym {[ true , ℕ.suc abs ]} {[ false , ℕ.suc abs' ]} ()
cf-sym {[ true , ℕ.zero ]} {[ true , ℕ.zero ]} refl = refl
cf-sym {[ true , ℕ.zero ]} {[ true , ℕ.suc abs' ]} ()
cf-sym {[ true , ℕ.suc abs ]} {[ true , ℕ.zero ]} ()
cf-sym {[ true , ℕ.suc abs ]} {[ true , ℕ.suc .abs ]} refl = refl

postulate -- postulate until we fill in the cases
  cf-trans : {m n p : Z} → m ≡cf n → n ≡cf p → m ≡cf p

-- cf is involutive

cf-involutive : (n : Z) → cf (cf n) ≡ cf n
cf-involutive [ false , ℕ.zero  ] = refl
cf-involutive [ false , ℕ.suc _ ] = refl
cf-involutive [ true  , _       ] = refl

-- two zeros map to a single zero
Z→ℤ : Z → ℤ
Z→ℤ [ false , ℕ.zero ]    = + ℕ.zero
Z→ℤ [ false , ℕ.suc abs ] = -[1+ abs ]
Z→ℤ [ true  , abs ]       = + abs

-- zero maps to the positive zero
ℤ→Z : ℤ → Z
ℤ→Z (+_ n)     = [ true , n ]
ℤ→Z (-[1+_] n) = [ false , ℕ.suc n ]

-- inverses

ℤ→Z→ℤ : (n : ℤ) → Z→ℤ (ℤ→Z n) ≡ n
ℤ→Z→ℤ (+_ n)     = refl
ℤ→Z→ℤ (-[1+_] n) = refl

Z→ℤ→Z : (n : Z) → ℤ→Z (Z→ℤ n) ≡cf n
Z→ℤ→Z [ false , ℕ.zero ]    = refl
Z→ℤ→Z [ false , ℕ.suc abs ] = refl
Z→ℤ→Z [ true  , abs ]       = refl

-- transport

transport : {A : Set} → (P : A → Set) → (x y : A) → x ≡ y → P x → P y
transport P _ _ refl px = px

-- plus

_+_ : Z → Z → Z
m + n = ℤ→Z ((Z→ℤ m) ℤ+ (Z→ℤ n))

_⊕_ : Z → Z → Z
[  false , ma ]       ⊕ [ false , na ]       = [ false , ma ℕ+ na ]
[  false , ℕ.zero ]   ⊕ [ true , na ]        = [ true , na ]
[  false , ℕ.suc ma ] ⊕ [ true , ℕ.zero ]    = [ false , ℕ.suc ma ]
[  false , ℕ.suc ma ] ⊕ [ true , ℕ.suc na ]  = [ false , ma ] ⊕ [ true , na ]
[  true , ℕ.zero ]    ⊕ [ false , na ]       = [ false , na ]
[  true , ℕ.suc ma ]  ⊕ [ false , ℕ.zero ]   = [ true , ℕ.suc ma ]
[  true , ℕ.suc ma ]  ⊕ [ false , ℕ.suc na ] = [ true , ma ] ⊕ [ false , na ]
[  true  , ma ]       ⊕ [ true  , na ]       = [ true , ma ℕ+ na ]
-- NOTE: The gray shading above (unreachable case) seems to be an Agda bug.

postulate -- posulate these until we fill in all the cases
  ⊕≡+ : (m n : Z) → m ⊕ n ≡ m + n
{-
⊕≡+ [ false , ℕ.zero ]    [ false , ℕ.zero ]     = {!!}
⊕≡+ [ false , ℕ.zero ]    [ false , ℕ.suc abs' ] = refl
⊕≡+ [ false , ℕ.zero ]    [ true  , ℕ.zero ]     = refl
⊕≡+ [ false , ℕ.zero ]    [ true  , ℕ.suc abs' ] = refl
⊕≡+ [ false , ℕ.suc abs ] [ false , ℕ.zero ]     rewrite (+-right-identity abs) = {!!}
⊕≡+ [ false , ℕ.suc abs ] [ false , ℕ.suc abs' ] = {!!}
⊕≡+ [ false , ℕ.suc abs ] [ true  , ℕ.zero ]     = {!!}
⊕≡+ [ false , ℕ.suc abs ] [ true  , ℕ.suc abs' ] = {!!}
⊕≡+ [ true  , ℕ.zero ]    [ false , ℕ.zero ]     = {!!}
⊕≡+ [ true  , ℕ.zero ]    [ false , ℕ.suc abs' ] = refl
⊕≡+ [ true  , ℕ.zero ]    [ true  , ℕ.zero ]     = refl
⊕≡+ [ true  , ℕ.zero ]    [ true  , ℕ.suc abs' ] = refl
⊕≡+ [ true  , ℕ.suc abs ] [ false , ℕ.zero ]     = {!!}
⊕≡+ [ true  , ℕ.suc abs ] [ false , ℕ.suc abs' ] = {!!}
⊕≡+ [ true  , ℕ.suc abs ] [ true  , ℕ.zero ]     = refl
⊕≡+ [ true  , ℕ.suc abs ] [ true  , ℕ.suc abs' ] = refl
-}

  ⊕≡cf+ : (m n : Z) → m ⊕ n ≡cf m + n
{-
⊕≡cf+ [ false , ℕ.zero    ] [ false , ℕ.zero ]     = refl
⊕≡cf+ [ false , ℕ.zero    ] [ false , ℕ.suc abs' ] = refl
⊕≡cf+ [ false , ℕ.suc abs ] [ false , ℕ.zero ]     = {!!}
⊕≡cf+ [ false , ℕ.suc abs ] [ false , ℕ.suc abs' ] = {!!}
⊕≡cf+ [ false , ℕ.zero    ] [ true , ℕ.zero ]      = refl
⊕≡cf+ [ false , ℕ.zero    ] [ true , ℕ.suc abs' ]  = refl
⊕≡cf+ [ false , ℕ.suc abs ] [ true , ℕ.zero ]      = refl
⊕≡cf+ [ false , ℕ.suc abs ] [ true , ℕ.suc abs' ]  = {!!}
⊕≡cf+ [ true  , ℕ.zero    ] [ false , ℕ.zero ]     = refl
⊕≡cf+ [ true  , ℕ.zero    ] [ false , ℕ.suc abs' ] = refl
⊕≡cf+ [ true  , ℕ.suc abs ] [ false , ℕ.zero ]     = {!!}
⊕≡cf+ [ true  , ℕ.suc abs ] [ false , ℕ.suc abs' ] = {!!}
⊕≡cf+ [ true  , ℕ.zero    ] [ true , ℕ.zero ]      = refl
⊕≡cf+ [ true  , ℕ.zero    ] [ true , ℕ.suc abs' ]  = refl
⊕≡cf+ [ true  , ℕ.suc abs ] [ true , ℕ.zero ]      = refl
⊕≡cf+ [ true  , ℕ.suc abs ] [ true , ℕ.suc abs' ]  = refl
-}

-- theorems

0+n≡n : (n : ℤ) → (+ 0) ℤ+ n ≡ n
0+n≡n (+_ n)     = refl
0+n≡n (-[1+_] n) = refl

Z0+n≡n : (n : Z) → [ true , 0 ] + n ≡cf n
Z0+n≡n n = transport
             (λ m → cf (ℤ→Z (+ 0 ℤ+ Z→ℤ n)) ≡ m)
             (cf (ℤ→Z (Z→ℤ n)))
             (cf n)
             (Z→ℤ→Z n)
             (cong (cf ∘ ℤ→Z) (0+n≡n (Z→ℤ n)))

