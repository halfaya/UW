\documentclass{article}
\usepackage{agda}
\usepackage{fullpage}

\begin{document}

Let me formalize in Agda something I'd said earlier in email. Here is
the original statement.

\begin{quote}
 I would view ornaments as a generalization of equivalences, and
 refinements as not really comparable to either. An equivalence is
 very precise and should be the easiest to automate. I think the Ko
 and Gibbons formulations of ornament (which I'm not sure is really
 "equivalent" to the McBride and Dagand formulation) is essentially
 an equivalence plus a refinement, so under this interpretation an
 equivalence could be seen as a degenerate ornament in which the
 refinement is trivial.
\end{quote}

\begin{code}[hide]
{-# OPTIONS --without-K --allow-unsolved-metas #-}

module EquivOrn where

open import Agda.Primitive                        using (Level; lzero; lsuc; _⊔_)
open import Data.Bool                             using (Bool)
open import Data.List                             using (List)
open import Data.Nat                              using (ℕ)
open import Data.Product                          using (Σ; _,_; _×_; proj₁)
open import Data.Vec                              using (Vec)
open import Data.Unit                             using (⊤; tt)
open import Function                              using (_∘_; id)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; refl; subst; sym; trans)
\end{code}

Let's define an equivalence; this is taken from \textit{Equivalences
for Free!} which in turn is taken from HoTT.

\begin{code}
record IsEquiv {a b : Level} (A : Set a) (B : Set b) (f : A → B) : Set (a ⊔ b) where
  constructor isEquiv
  field
    f⁻¹  : B → A
    sect : (a : A) → (f⁻¹ ∘ f) a ≡ a
    retr : (b : B) → (f ∘ f⁻¹) b ≡ b
    adj  : (a : A) → retr (f a) ≡ cong f (sect a)
open IsEquiv    

record Equiv {a b : Level} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  constructor equiv
  field
    func : A → B
    isEq : IsEquiv A B func
open Equiv
\end{code}

Here's the definition of heterogeneous relation from the Agda standard
library. Note that it's the same as the one in Talia's picture of the
blackboard, except it uses Set rather than Prop (although Agda now has
its own Prop due to recent work by Jesper Cockx, based on the new
sProp for Coq that Tabareau and other people are working on, done
during Jesper's visit to Nantes).

\begin{code}
REL : {a b : Level} → Set a → Set b → (ℓ : Level) → Set (a ⊔ b ⊔ lsuc ℓ)
REL A B ℓ = A → B → Set ℓ
\end{code}

When I think of a refinement however, I think of a type with a
predicate, which is the following, and it's important that the
codomain be Set in this case.

\begin{code}
Pred : {a : Level} → Set a → (ℓ : Level) → Set (a ⊔ lsuc ℓ)
Pred A ℓ = A → Set ℓ
\end{code}

I would then define a refinement as a pair of a type and a
predicate on that type. Let's create a new data type for clarity.

\begin{code}
data Refinement {a ℓ : Level} (A : Set a) (P : Pred A ℓ) : Set (a ⊔ ℓ) where
  refinement : (x : A) → P x → Refinement A P
\end{code}

If Talia has a different formulation in terms of a relation, I'd be
interested in seeing that.

We could describe ornamenting ℕ with a vector of booleans using a
refinement as follows.

\begin{code}
ornℕvecBool : Set
ornℕvecBool = Refinement ℕ (Vec Bool)
\end{code}

Now let me define an Ornament in a way that is similar to what Talia
is talking about. It's too general, since it encompasses things that
are not ornaments, and perhaps there are other flaws as well, but it's
simple and will give us something to refer to.

Define an Ornament to be an equivalence between a refinement of $A$
(the base type), where the refinement carries the extra information of
the ornament, and $B$, which is the fully-ornamented type, as the
following.

\begin{code}
Ornament : {a b ℓ : Level} (A : Set a) → (B : Set b) → Set (a ⊔ b ⊔ lsuc ℓ)
Ornament {ℓ = ℓ} A B = Σ (Pred A ℓ) (λ P → Equiv (Refinement A P) B)
\end{code}

Now, returning to my opening quote, I think of ornaments as strict
generalizations of equivalences. This first means the following type is inhabited.

\begin{code}[hide]
sect∘sect : {a b c : Level} {A : Set a} {B : Set b} {C : Set c} →
            (α : Equiv A B) → (β : Equiv B C)
            (x : A) → (f⁻¹ (isEq α) ∘ f⁻¹ (isEq β) ∘ func β ∘ func α) x ≡ x
sect∘sect α β x rewrite (sect (isEq β) ((func α) x )) | (sect (isEq α) x) = refl

retr∘retr : {a b c : Level} {A : Set a} {B : Set b} {C : Set c} →
            (α : Equiv A B) → (β : Equiv B C)
            (x : C) → (func β ∘ func α ∘ f⁻¹ (isEq α) ∘ f⁻¹ (isEq β)) x ≡ x
retr∘retr α β x rewrite retr (isEq α) ((f⁻¹ (isEq β)) x) | (retr (isEq β) x) = refl

-- Proof still to be given. Adjunctions are hard to prove.
adj∘adj : {a b c : Level} {A : Set a} {B : Set b} {C : Set c} →
          (α : Equiv A B) → (β : Equiv B C)
          (x : A) → retr∘retr α β ((func β ∘ func α) x) ≡ cong (func β ∘ func α) (sect∘sect α β x)
adj∘adj α β x = {!!}

equivTrans : {a b c : Level} {A : Set a} {B : Set b} {C : Set c} → Equiv A B → Equiv B C → Equiv A C
equivTrans α@(equiv f (isEquiv f₁ s r adj)) β@(equiv g (isEquiv g₁ s' r' adj')) =
  equiv (g ∘ f) (isEquiv (f₁ ∘ g₁) (sect∘sect α β) (retr∘retr α β) (adj∘adj α β))

A≃A×⊤ : {a : Level}{A : Set a} → Equiv A (A × ⊤)
A≃A×⊤ = equiv (_, tt) (isEquiv proj₁ (λ _ → refl) (λ _ → refl) (λ _ → refl))

π₁ : {a : Level} {A : Set a} → Refinement A (λ _ → ⊤) → A
π₁ (refinement a tt) = a

lemma : {a : Level}{A : Set a} → (R : Refinement A (λ _ → ⊤)) → refinement (π₁ R) tt ≡ R
lemma (refinement a tt) = refl

lemma2 : {a : Level}{A : Set a} → (R : Refinement A (λ _ → ⊤)) → refl ≡ cong π₁ (lemma R)
lemma2 (refinement a tt) = refl

RefA≃A : {a : Level}{A : Set a} → Equiv (Refinement A (λ _ → ⊤)) A
RefA≃A = equiv π₁ (isEquiv (λ a → refinement a tt) lemma (λ b → refl) lemma2)

\end{code}

\begin{code}
Equivalence→Ornament : {a b : Level}{A : Set a} → {B : Set b} → Equiv A B → Ornament A B
Equivalence→Ornament eq = (λ _ → ⊤) , equivTrans RefA≃A eq
\end{code}

As can be seen the proof here is extremely simple, modulo some lemmas
which are straigthfoward.  Note the trivial refinement.  The lemmas
have been hidden from the generated PDF but are in the source file. I
believe it would be straightforward as well to prove that every
equivalance is an ornament in either the McBride/Dagand or Ko/Gibbons
formulations.

By Propositions as Types (PAT), this is interpreted as: If there is
an equivalance between $A$ and $B$, then there is also an ornament
between $A$ and $B$.

On the other hand the converse is not true.
\begin{code}
Ornament→Equivalence : {a b ℓ : Level}{A : Set a} → {B : Set b} → Ornament {ℓ = ℓ} A B → Equiv A B
Ornament→Equivalence orn = {!!}
\end{code}

There is no way to fill in the hole above.  A counterexample is that
there is an ornament from $ℕ$ to \textit{List Bool} but the two are
not equivalent. Thus ornaments are a strict generalization of
equivalences.

Similarly when I said refinements are not comparable to either, I
meant there is no function from refinemennts to or from either
equivalances or ornaments.

I believe what Talia was talking about is that equivalances can be
defined in terms of relations, and ornaments can be defined in terms
of equivalances (but as noted it will not be an equivalence of the
original types).

\end{document}
