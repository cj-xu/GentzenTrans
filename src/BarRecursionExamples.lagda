
 ===============================================================
 =                                                             =
 =  Application: Uniform Continuity via General Bar Recursion  =
 =                                                             =
 ===============================================================

    Chuangjie Xu, May 2020

    Updated in November 2026


We implement the reviewer's example of defining moduli of uniform
continuity using functionals of general bar recursion.

Update in November 2026:

- Proved the correctness of the constructed modulus.

\begin{code}

{-# OPTIONS --without-K --safe #-}

open import Preliminaries
open import T
open import TAuxiliaries
open import GeneralBarRecursion ι public
open import UniformContinuity

\end{code}

For a fixed bound δ, `MB t δ` starts the recursion at the empty sequence.
If the current sequence secures `t`, the base case returns 0. Otherwise,
the step takes one plus the maximum of the recursive bounds for the
possible next inputs i ≤ δ(length s).

\begin{code}

⟨⟩ : ℕ*
⟨⟩ = (λ n → n) , 0

MB : T ε (ιᶥ ⇾ ι) → ℕᴺ → ℕ
MB t δ = ⟦ 𝐠𝐛𝐫 t ⟧ G H ⟨⟩
 where
  G : ℕ* → ℕ
  G _ = 0
  H : ℕ* → ℕᴺ → ℕ
  H (_ , n) f = suc (⟦ Φ ⟧ f (δ n))

\end{code}

The proof below assumes function extensionality through Thm[GBR].

For a prefix s, let B s be the same bar-recursive bound started at s.
If B s ≤ m, two inputs bounded by δ that extend s and agree on the next
m entries have the same value under t. We prove this by induction on m.
At a secured prefix, security gives equality immediately. Otherwise,
the maximum in the step bounds the child selected by α (len s), since
this entry is at most δ (len s), and the induction hypothesis applies.

\begin{code}

MB-correct : FunExt
           → (t : T ε (ιᶥ ⇾ ι))
           → MB t is-a-modulus-of-uniform-continuity-of ⟦ t ⟧
MB-correct fe t {δ} {α} {β} α≤δ _ agreement =
  lemma (B ⟨⟩) ⟨⟩ ≤refl (λ i ()) (λ i ()) agreement
 where
  S : ℕ* → ℕ
  S = ⟦ 𝐒 t ⟧
  G : ℕ* → ℕ
  G _ = 0
  H : ℕ* → ℕᴺ → ℕ
  H s f = suc (⟦ Φ ⟧ f (δ (len s)))
  B : ℕ* → ℕ
  B = ⟦ 𝐠𝐛𝐫 t ⟧ G H

  facts = Thm[GBR] fe t
  SsY : S secures ⟦ t ⟧
  SsY = pr₁ (pr₂ facts)
  gbr : GBR S ⟦ 𝐠𝐛𝐫 t ⟧
  gbr = pr₂ (pr₂ facts)

  secured : (s : ℕ*) → s ∈ S → s ∋ α → s ∋ β
          → ⟦ t ⟧ α ≡ ⟦ t ⟧ β
  secured s sS sα sβ = trans (sym (SsY s sS α sα)) (SsY s sS β sβ)

  lemma : (m : ℕ) (s : ℕ*) → B s ≤ m → s ∋ α → s ∋ β
     → drop (len s) α ≡[ m ] drop (len s) β
     → ⟦ t ⟧ α ≡ ⟦ t ⟧ β
  lemma 0 s Bs≤0 sα sβ e = case (λ sS → secured s sS sα sβ) impossible (∈-dec S)
   where
    impossible : s ∉ S → ⟦ t ⟧ α ≡ ⟦ t ⟧ β
    impossible nsS = 𝟘-elim (suc≰zero
      (transport (λ k → k ≤ 0) (pr₂ (gbr G H s) nsS) Bs≤0))
  lemma (suc m) s Bs≤m sα sβ (≡[suc] e es) =
    case (λ sS → secured s sS sα sβ) descend (∈-dec S)
   where
    n : ℕ
    n = α (len s)
    sn : ℕ*
    sn = s ✦ n
    next-equal : n ≡ β (len s)
    next-equal = trans (sym (drop-head (len s) α))
                       (trans e (drop-head (len s) β))
    snα : sn ∋ α
    snα = ✦-prefix s α sα refl
    snβ : sn ∋ β
    snβ = ✦-prefix s β sβ next-equal
    next-agreement : drop (len sn) α ≡[ m ] drop (len sn) β
    next-agreement = transport (λ k → drop k α ≡[ m ] drop k β)
      (len✦-suc s) (drop-agreement (len s) es)
    descend : s ∉ S → ⟦ t ⟧ α ≡ ⟦ t ⟧ β
    descend nsS = lemma m sn child-bound snα snβ next-agreement
     where
      max-bound : ⟦ Φ ⟧ (λ i → B (s ✦ i)) (δ (len s)) ≤ m
      max-bound = ≤-pred
        (transport (λ k → k ≤ suc m) (pr₂ (gbr G H s) nsS) Bs≤m)
      child-bound : B sn ≤ m
      child-bound = ≤trans
        (Φ-spec (α≤δ (len s)) ⋆ (λ i → B (s ✦ i))) max-bound

\end{code}
