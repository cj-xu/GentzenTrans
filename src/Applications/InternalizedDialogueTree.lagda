
 ===============================================
 =                                             =
 =  Application: Church-Encoded Dialogue Tree  =
 =                                             =
 ===============================================

    Chuangjie Xu, April 2026

    updated in November 2026

This module extracts a Church-encoded dialogue tree from each
closed System T term of type `(ι ⇾ ι) ⇾ ι`. We prove that the
extracted term encodes an inductively defined dialogue tree
whose evaluation agrees with the interpretation of the
original term at every oracle.

The module is inspired by Escardó et al. [1]. We obtain the
extraction and its correctness by instantiating our Gentzen
translation and its fundamental theorem. We use an inductively
defined encoding relation, while [1] compares Church values
with canonical encodings using hereditarily extensional equality.


Update in November 2026:

- Introduced an inductive relation expressing that a Church value
  encodes a dialogue tree.

- Strengthened the logical relation to carry a dialogue tree,
  encoding evidence, and evaluation correctness.

- Strengthened the main theorem to exhibit a dialogue tree encoded
  by the extracted term.


References

[1] M.H. Escardó, B. da Rocha Paiva, V. Rahli, and A. Tosun.
    Internal Effectful Forcing in System T. FSCD 2025,
    LIPIcs 337, pp. 19:1-19:17, 2025.

\begin{code}

{-# OPTIONS --without-K --safe #-}

module Applications.InternalizedDialogueTree where

open import Preliminaries
open import SystemT.Base
open import SystemT.Auxiliaries

\end{code}

■ Inductively defined dialogue trees in Agda

We begin with the ordinary inductive type of dialogue trees. A
tree is either a leaf `η n`, which immediately returns `n`, or
a branching node `β g i`, which queries the oracle at `i` and
continues with the subtree selected by the answer.

\begin{code}

data D : Set where
  η : ℕ → D
  β : (ℕ → D) → ℕ → D

eval : D → ℕᴺ → ℕ
eval (η n) _ = n
eval (β g i) α = eval (g (α i)) α

\end{code}

The Kleisli extension `κ f` replaces each leaf `η n` with
the tree `f n`.

\begin{code}

κ : (ℕ → D) → D → D
κ f (η n)   = f n
κ f (β φ i) = β (λ j → κ f (φ j)) i

eval-κ : (f : ℕ → D) (d : D) (α : ℕᴺ)
       → eval (κ f d) α ≡ eval (f (eval d α)) α
eval-κ f (η n)   α = refl
eval-κ f (β φ i) α = eval-κ f (φ (α i)) α

\end{code}

■ Church encodings of dialogue trees in System T

We next define the corresponding Church encoding in System T.
The terms `ηᵀ` and `βᵀ` encode leaves and queries.
The operation `κᵀ` supplies Kleisli extension for the
translation, and `Ωᵀ` is the generic element used to extract
a dialogue tree.

\begin{code}

Dᵀ : Ty → Ty
Dᵀ ρ = (ι ⇾ ρ) ⇾ ((ι ⇾ ρ) ⇾ ι ⇾ ρ) ⇾ ρ

ηᵀ : {ρ : Ty} {Γ : Cxt}
   → T Γ (ι ⇾ Dᵀ ρ)
ηᵀ = Lam (Lam (Lam (ν₁ · ν₂)))

βᵀ : {ρ : Ty} {Γ : Cxt}
   → T Γ ((ι ⇾ Dᵀ ρ) ⇾ ι ⇾ Dᵀ ρ)
βᵀ = Lam (Lam (Lam (Lam (ν₀ · Lam (ν₄ · ν₀ · ν₂ · ν₁) · ν₂))))

κᵀ : {ρ : Ty} {Γ : Cxt}
   → T Γ ((ι ⇾ Dᵀ ρ) ⇾ Dᵀ ρ ⇾ Dᵀ ρ)
κᵀ = Lam (Lam (Lam (Lam (ν₂ · Lam (ν₄ · ν₀ · ν₂ · ν₁) · ν₀))))

Ωᵀ : {ρ : Ty} {Γ : Cxt}
   → T Γ (Dᵀ ρ ⇾ Dᵀ ρ)
Ωᵀ = κᵀ · (βᵀ · ηᵀ)

\end{code}

We specialise the result type `ρ` to `(ι ⇾ ι) ⇾ ι` so that
a Church-encoded tree can be interpreted as a functional on
oracles.

We write `Dᵀ₂` for the resulting Church-encoded tree type.

\begin{code}

Dᵀ₂ : Ty
Dᵀ₂ = Dᵀ (typeᵀ 2)

open import Framework.Gentzen.Translation Dᵀ₂ ηᵀ κᵀ

dialogue-treeᵀ : T ε ((ι ⇾ ι) ⇾ ι) → T ε Dᵀ₂
dialogue-treeᵀ t = t ᴶ · Ωᵀ

\end{code}

■ Evaluation of Church-encoded dialogue trees

The Church representation allows us to define evaluation within
System T by supplying interpretations of leaves and queries.
The operations `leaf` and `branch` correspond to the two clauses
of the inductive evaluator `eval`.

\begin{code}

leafᵀ : {Γ : Cxt}
      → T Γ (ι ⇾ typeᵀ 2)
leafᵀ = Lam (Lam ν₁)

leaf : ℕ → type 2
leaf n α = n

leafᵀ-interpretation : {Γ : Cxt} {γ : ⟦ Γ ⟧ˣ}
                     → ⟦ leafᵀ ⟧ᵐ γ ≡ leaf
leafᵀ-interpretation = refl

branchᵀ : {Γ : Cxt}
        → T Γ ((ι ⇾ typeᵀ 2) ⇾ ι ⇾ typeᵀ 2)
branchᵀ = Lam (Lam (Lam (ν₂ · (ν₀ · ν₁) · ν₀)))

branch : (ℕ → type 2) → ℕ → type 2
branch g i α = g (α i) α

branchᵀ-interpretation : {Γ : Cxt} {γ : ⟦ Γ ⟧ˣ}
                       → ⟦ branchᵀ ⟧ᵐ γ ≡ branch
branchᵀ-interpretation = refl

evalᵀ : {Γ : Cxt}
      → T Γ (Dᵀ₂ ⇾ (ι ⇾ ι) ⇾ ι)
evalᵀ = Lam (ν₀ · leafᵀ · branchᵀ)

\end{code}

■ The encoding relation between Church values and dialogue trees

The type `⟦ Dᵀ₂ ⟧ʸ` contains arbitrary functions of the leaf and query
interpretations. Having this type alone does not ensure that a value
represents an inductive dialogue tree. We therefore define an encoding
relation that identifies values built from the Church constructors
according to the structure of such a tree.

\begin{code}

data _encodes_ : ⟦ Dᵀ₂ ⟧ʸ → D → Set where
 enc-η : (n : ℕ)
       → (⟦ ηᵀ ⟧ n) encodes (η n)
 enc-β : {g : ℕ → ⟦ Dᵀ₂ ⟧ʸ} {φ : ℕ → D}
       → ((j : ℕ) → (g j) encodes (φ j))
       → (i : ℕ)
       → (⟦ βᵀ ⟧ g i) encodes (β φ i)

\end{code}

The Church Kleisli extension κᵀ preserves the encoding relation.

\begin{code}

enc-κ : {g : ℕ → ⟦ Dᵀ₂ ⟧ʸ} {f : ℕ → D} {t : ⟦ Dᵀ₂ ⟧ʸ} {d : D}
      → ((i : ℕ) → (g i) encodes (f i))
      → t encodes d
      → (⟦ κᵀ ⟧ g t) encodes (κ f d)
enc-κ p (enc-η n) = p n
enc-κ p (enc-β q i) = enc-β (λ j → enc-κ p (q j)) i

\end{code}

Evaluating a Church value with `leaf` and `branch` gives the same result
as evaluating its encoded tree. Consequently, two trees encoded by the
same Church value agree at every oracle.

\begin{code}

encodes-eval : {t : ⟦ Dᵀ₂ ⟧ʸ} {d : D}
             → t encodes d
             → (α : ℕᴺ) → t leaf branch α ≡ eval d α
encodes-eval (enc-η n)   α = refl
encodes-eval (enc-β p i) α = encodes-eval (p (α i)) α

encodes-eval-agree : {t : ⟦ Dᵀ₂ ⟧ʸ} {d d' : D}
                   → t encodes d
                   → t encodes d'
                   → (α : ℕᴺ) → eval d α ≡ eval d' α
encodes-eval-agree enc enc' α
 = trans (sym (encodes-eval enc α)) (encodes-eval enc' α)

\end{code}

■ Logical relation

The base relation Rι expresses the desired property of the translated
value: it must encode a dialogue tree whose evaluation at the fixed
oracle gives the original value.

\begin{code}

Rι : ℕᴺ → ℕ → ⟦ Dᵀ₂ ⟧ʸ → Set
Rι α n t = Σ \(d : D) → (t encodes d) × (n ≡ eval d α)

Rη : (α : ℕᴺ)
   → {Γ : Cxt} (γ : ⟦ Γ ⟧ˣ) (n : ℕ)
   → Rι α n (⟦ ηᵀ ⟧ᵐ γ n)
Rη α γ n = η n , enc-η n , refl

Rκ : (α : ℕᴺ)
   → {Γ : Cxt} (γ : ⟦ Γ ⟧ˣ)
   → {f : ℕ → ℕ} {g : ℕ → ⟦ Dᵀ₂ ⟧ʸ}
   → (∀ i → Rι α (f i) (g i))
   → ∀ {n : ℕ} {t : ⟦ Dᵀ₂ ⟧ʸ}
   → Rι α n t
   → Rι α (f n) (⟦ κᵀ ⟧ᵐ γ g t)
Rκ α γ {f} {g} ζ {n} (d , enc , eq) = κ ζ₀ d , enc-κ ζ₁ enc , eq'
 where
  ζ₀ : ℕ → D
  ζ₀ i = pr₁ (ζ i)
  ζ₁ : (i : ℕ) → (g i) encodes (ζ₀ i)
  ζ₁ i = pr₁ (pr₂ (ζ i))
  ζ₂ : (i : ℕ) → f i ≡ eval (ζ₀ i) α
  ζ₂ i = pr₂ (pr₂ (ζ i))
  e₀ : f n ≡ eval (ζ₀ n) α
  e₀ = ζ₂ n
  e₁ : eval (ζ₀ n) α ≡ eval (ζ₀ (eval d α)) α
  e₁ = ap (λ x → eval (ζ₀ x) α) eq
  e₂ : eval (κ ζ₀ d) α ≡ eval (ζ₀ (eval d α)) α
  e₂ = eval-κ ζ₀ d α
  eq' : f n ≡ eval (κ ζ₀ d) α
  eq' = trans e₀ (trans e₁ (sym e₂))

RΩ : (α : ℕᴺ)
   → ∀ {n t} → Rι α n t
   → Rι α (α n) (⟦ Ωᵀ ⟧ t)
RΩ α = Rκ α ⋆ fact
 where
  fact : (i : ℕ) → Rι α (α i) (⟦ βᵀ ⟧ ⟦ ηᵀ ⟧ i)
  fact i = β η i , enc-β enc-η i , refl

\end{code}

■ Correctness of extraction

The fundamental theorem implies that for each closed term t of type 2,
⟦ dialogue-treeᵀ t ⟧ encodes a dialogue tree whose evaluation agrees
with ⟦ t ⟧ at every oracle.

\begin{code}

Thm[InternalDialogue]
 : (t : T ε ((ι ⇾ ι) ⇾ ι))
 → Σ \(d : D) → (⟦ dialogue-treeᵀ t ⟧ encodes d)
              × ((α : ℕᴺ) → ⟦ t ⟧ α ≡ eval d α)
Thm[InternalDialogue] t = d , enc , eq
 where
  cor : (α : ℕᴺ) → Rι α (⟦ t ⟧ α) ⟦ dialogue-treeᵀ t ⟧
  cor α = LR.FTLR t ⋆ (RΩ α)
   where
    import Framework.Gentzen.LogicalRelation Dᵀ₂ ηᵀ κᵀ
      (Rι α) (Rη α) (Rκ α) as LR
  d : D
  d = pr₁ (cor 0ʷ)
  enc : ⟦ dialogue-treeᵀ t ⟧ encodes d
  enc = pr₁ (pr₂ (cor 0ʷ))
  eq : (α : ℕᴺ) → ⟦ t ⟧ α ≡ eval d α
  eq α using (_ , encα , eqα) ← cor α
   = trans eqα (encodes-eval-agree encα enc α)

\end{code}

Evaluating the extracted Church-encoded tree in System T
recovers the functional denoted by the original term.

\begin{code}

Cor[evalᵀdialogue-treeᵀ]
 : (t : T ε ((ι ⇾ ι) ⇾ ι))
 → (α : ℕᴺ) → ⟦ t ⟧ α ≡ ⟦ evalᵀ · dialogue-treeᵀ t ⟧ α
Cor[evalᵀdialogue-treeᵀ] t α
 using (d , enc , eq) ← Thm[InternalDialogue] t
 = trans e₀ (sym e₁)
 where
  e₀ : ⟦ t ⟧ α ≡ eval d α
  e₀ = eq α
  e₁ : ⟦ evalᵀ · dialogue-treeᵀ t ⟧ α ≡ eval d α
  e₁ = encodes-eval enc α

\end{code}
