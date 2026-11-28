Chuangjie Xu, November 2026

Generic elements for the Gentzen-style translation

A generic element Ω supplies a single argument to a translated function
f ᴶ. Once the fundamental theorem relates f to its translation, genericity
lets us relate the value of f at each input to the interpretation of
f ᴶ · Ω.

\begin{code}

{-# OPTIONS --without-K --safe #-}

open import SystemT.Base

module Framework.Gentzen.Genericity
  (Jι : Ty)
  (η : {Γ : Cxt} → T Γ (ι ⇾ Jι))
  (κ : {Γ : Cxt} → T Γ ((ι ⇾ Jι) ⇾ Jι ⇾ Jι))
  (X : Ty)
  (Rι : ⟦ X ⟧ʸ → ⟦ ι ⟧ʸ → ⟦ Jι ⟧ʸ → Set)
  where

open import Framework.Gentzen.Translation Jι η κ using (⟨_⟩ᴶ)
import Framework.Gentzen.LogicalRelation Jι η κ as GentzenLR

is-generic : {Γ : Cxt} → T Γ ⟨ X ⟩ᴶ → Set
is-generic {Γ} Ω = (γ : ⟦ Γ ⟧ˣ) (x : ⟦ X ⟧ʸ) → LR._R_ x x (⟦ Ω ⟧ᵐ γ)
 where
  module LR (x : ⟦ X ⟧ʸ) = GentzenLR (Rι x)

\end{code}
