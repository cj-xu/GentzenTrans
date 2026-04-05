Chuangjie Xu 2026

This module studies Church-encoded dialogue trees in Gödel's
System T. The main goal is to extract, from a closed term of
type `(ι ⇾ ι) ⇾ ι`, a Church-encoded dialogue tree and to prove
its correctness in the sense that its evaluation agrees with
the standard set-theoretic interpretation of the original term.

The module is inspired by Escardó, da Rocha Paiva, Rahli, and
Tosun, _Internal Effectful Forcing in System T_ (FSCD 2025,
LIPIcs 337, Article 19, DOI `10.4230/LIPIcs.FSCD.2025.19`).
Their paper uses internal effectful forcing to show, among
other things, that the dialogue tree associated to a System T
term is itself definable in System T via a Church encoding of
trees.

Our treatment here is more modest and more direct. We use a
logical relation between the standard interpretation of
System T and its Church-encoded dialogue-tree interpretation,
together with an explicit representation relation between
Church values and inductive dialogue trees. This is enough to
prove that the extracted Church-encoded dialogue tree
computes the same type-2 functional as the original System T
term.

\begin{code}

{-# OPTIONS --without-K --safe #-}

module InternalizedDialogueTree where

open import Preliminaries
open import T

\end{code}

Inductively defined dialogue trees in Agda

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

κ : (ℕ → D) → D → D
κ f (η n) = f n
κ f (β g i) = β (λ n → κ f (g n)) i

Ω : D → D
Ω = κ (β η)

\end{code}

Church encodings of dialogue trees in System T

We next define the corresponding Church encoding in System T.
The terms `ηᵀ`, `βᵀ`, `κᵀ`, and `Ωᵀ` are the encoded
counterparts of the operations on the inductive trees above.

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

From now on we specialise the result type `ρ` to the type-2
functional type `(ι ⇾ ι) ⇾ ι`. We write `typeᵀ-2` for this
System T type, `type-2` for its Agda interpretation `ℕᴺ → ℕ`,
and `Dᵀ₂` for the resulting Church-encoded tree type.

\begin{code}

typeᵀ-2 : Ty
typeᵀ-2 = (ι ⇾ ι) ⇾ ι

type-2 : Set
type-2 = ℕᴺ → ℕ

Dᵀ₂ : Ty
Dᵀ₂ = Dᵀ typeᵀ-2

\end{code}

Evaluation of Church-encoded dialogue trees

To evaluate a Church-encoded dialogue tree, we instantiate it
with the same leaf and branching algebra used by the inductive
evaluator. The operation `leaf` interprets leaves, while
`branch` interprets branching by querying the oracle at the
given index and continuing with the selected branch. The terms
`leafᵀ` and `branchᵀ` are their System T counterparts, and the
following lemmas record that their denotations are exactly the
intended Agda functions.

\begin{code}

branchᵀ : {Γ : Cxt}
        → T Γ ((ι ⇾ typeᵀ-2) ⇾ ι ⇾ typeᵀ-2)
branchᵀ = Lam (Lam (Lam (ν₂ · (ν₀ · ν₁) · ν₀)))

branch : (ℕ → type-2) → ℕ → type-2
branch g i α = g (α i) α

branchᵀ-interpretation : {Γ : Cxt} {γ : ⟦ Γ ⟧ˣ}
                       → ⟦ branchᵀ ⟧ᵐ γ ≡ branch
branchᵀ-interpretation = refl

leafᵀ : {Γ : Cxt}
      → T Γ (ι ⇾ typeᵀ-2)
leafᵀ = Lam (Lam ν₁)

leaf : ℕ → type-2
leaf n α = n

leafᵀ-interpretation : {Γ : Cxt} {γ : ⟦ Γ ⟧ˣ}
                     → ⟦ leafᵀ ⟧ᵐ γ ≡ leaf
leafᵀ-interpretation = refl

evalᵀ : {Γ : Cxt}
      → T Γ (Dᵀ₂ ⇾ (ι ⇾ ι) ⇾ ι)
evalᵀ = Lam (ν₀ · leafᵀ · branchᵀ)

\end{code}

Representable Church values

The semantic type `⟦ Dᵀ₂ ⟧ʸ` is a higher-order function space,
so its elements need not satisfy the fold laws of genuine
dialogue trees. Accordingly, we restrict attention to those
Church values that are represented by actual inductive
dialogue trees.

To do this, we define `run`, which interprets an inductive
dialogue tree in the same leaf and branching algebra as the
Church encoding. We then say that a dialogue tree `d`
represents a Church value `t` when both give the same result
for every leaf algebra `e` and every oracle `α`.

\begin{code}

run : D → (ℕ → type-2) → type-2
run (η n) e α = e n α
run (β g i) e α = run (g (α i)) e α

_represents_ : D → ⟦ Dᵀ₂ ⟧ʸ → Set
d represents t = ∀ (e : ℕ → type-2) (α : ℕᴺ) → t e branch α ≡ run d e α

\end{code}

The first lemma shows that `run` agrees with the ordinary
evaluator when the leaf algebra is `leaf`. From this we obtain
the correctness of `evalᵀ` on represented Church values.

\begin{code}

run-eval : (t : D) (α : ℕᴺ) → run t leaf α ≡ eval t α
run-eval (η n) α = refl
run-eval (β g i) α = run-eval (g (α i)) α

evalᵀ-correct : {Γ : Cxt} (γ : ⟦ Γ ⟧ˣ)
              → (d : D) (t : ⟦ Dᵀ₂ ⟧ʸ) → d represents t
              → ∀ (α : ℕᴺ) → ⟦ evalᵀ ⟧ᵐ γ t α ≡ eval d α
evalᵀ-correct _ d _ r α = trans (r leaf α) (run-eval d α)

\end{code}

Compatibility with `κ`

To prove preservation under `κᵀ`, we use two auxiliary facts.
The lemma `run-ext` says that changing the leaf algebra
pointwise does not change the result of `run`. The lemma
`run-κ` states that the inductive operation `κ` is interpreted
by composing `run` with the continuation. Using these, we show
that representation is preserved by `κᵀ`.

\begin{code}

run-ext : (t : D) {e₀ e₁ : ℕ → type-2}
        → (∀ n α → e₀ n α ≡ e₁ n α)
        → ∀ α → run t e₀ α ≡ run t e₁ α
run-ext (η n) ξ α = ξ n α
run-ext (β g i) ξ α = run-ext (g (α i)) ξ α

run-κ : (h : ℕ → D) (t : D) (e : ℕ → type-2) (α : ℕᴺ)
      → run (κ h t) e α ≡ run t (λ n → run (h n) e) α
run-κ h (η n) e α = refl
run-κ h (β g i) e α = run-κ h (g (α i)) e α

κᵀ-preserves-representation : {Γ : Cxt} (γ : ⟦ Γ ⟧ˣ)
                            → (g : ℕ → D) (h : ℕ → ⟦ Dᵀ₂ ⟧ʸ)
                            → (∀ i → g i represents (h i))
                            → (d : D) (t : ⟦ Dᵀ₂ ⟧ʸ)
                            → d represents t
                            → κ g d represents ⟦ κᵀ ⟧ᵐ γ h t
κᵀ-preserves-representation _ g h ζ d t r e α = goal
 where
  claim₀ : t (λ n → h n e branch) branch α ≡ run d (λ n → h n e branch) α
  claim₀ = r (λ n → h n e branch) α
  claim₁ : run d (λ n → h n e branch) α ≡ run d (λ n → run (g n) e) α
  claim₁ = run-ext d (λ n β → ζ n e β) α
  claim₂ : run d (λ n → run (g n) e) α ≡ run (κ g d) e α
  claim₂ = sym (run-κ g d e α)
  goal : t (λ n → h n e branch) branch α ≡ run (κ g d) e α
  goal = trans claim₀ (trans claim₁ claim₂)

\end{code}

Logical relation

We now instantiate the generic Gentzen translation with the
Church encoding `Dᵀ₂`. The Church-encoded dialogue tree
`dialogue-treeᵀ t` is obtained from `t` by applying its
translation to `Ωᵀ`.

The base relation `Rι` says that a Church value is related to a
natural number when it is represented by some inductive
dialogue tree that evaluates to that number at the oracle `α`.
The clauses `Rη`, `Rκ`, and `RΩ` verify that the nucleus
preserves this relation, so the generic logical-relation
machinery applies.

\begin{code}

open import GentzenTranslation Dᵀ₂ ηᵀ κᵀ

dialogue-treeᵀ : T ε ((ι ⇾ ι) ⇾ ι) → T ε Dᵀ₂
dialogue-treeᵀ t = t ᴶ · Ωᵀ

Rι : ℕᴺ → ⟦ ι ⟧ʸ → ⟦ Dᵀ₂ ⟧ʸ → Set
Rι α n t = Σ \(d : D) → (d represents t) × (n ≡ eval d α)

Rη : (α : ℕᴺ)
   → {Γ : Cxt} (γ : ⟦ Γ ⟧ˣ) (n : ⟦ ι ⟧ʸ) → Rι α n (⟦ ηᵀ ⟧ᵐ γ n)
Rη _ _ n = η n , (λ _ _ → refl) , refl

eval-κ : (h : ℕ → D) (t : D) (α : ℕᴺ)
       → eval (κ h t) α ≡ eval (h (eval t α)) α
eval-κ h (η n) α = refl
eval-κ h (β g i) α = eval-κ h (g (α i)) α

Rκ : (α : ℕᴺ)
   → {Γ : Cxt} (γ : ⟦ Γ ⟧ˣ)
   → {f : ⟦ ι ⇾ ι ⟧ʸ} {g : ⟦ ι ⇾ Dᵀ₂ ⟧ʸ} → (∀ i → Rι α (f i) (g i))
   → ∀ {n : ⟦ ι ⟧ʸ} {t : ⟦ Dᵀ₂ ⟧ʸ} → Rι α n t
   → Rι α (f n) (⟦ κᵀ ⟧ᵐ γ g t)
Rκ α γ {f} {g} ζ {n} {t} (d , r , refl) = κ h d , rep , value
 where
  h : ℕ → D
  h i = pr₁ (ζ i)
  ζ' : ∀ i → (h i) represents (g i)
  ζ' i = pr₁ (pr₂ (ζ i))
  rep : κ h d represents ⟦ κᵀ ⟧ᵐ γ g t
  rep = κᵀ-preserves-representation γ h g ζ' d t r
  base : f (eval d α) ≡ eval (h (eval d α)) α
  base = pr₂ (pr₂ (ζ (eval d α)))
  step : eval (κ h d) α ≡ eval (h (eval d α)) α
  step = eval-κ h d α
  value : f (eval d α) ≡ eval (κ h d) α
  value = trans base (sym step)

RΩ : (α : ℕᴺ)
   → ∀ {n t} → Rι α n t → Rι α (α n) (⟦ Ωᵀ ⟧ t)
RΩ α {n} {t} (d , r , refl) = Ω d , rep , value
 where
  rep : (Ω d) represents (⟦ Ωᵀ ⟧ t)
  rep = κᵀ-preserves-representation ⋆ (β η) ⟦ βᵀ · ηᵀ ⟧ (λ _ _ _ → refl) d t r
  value : α (eval d α) ≡ eval (Ω d) α
  value = sym (eval-κ (β η) d α)

R : ℕᴺ → {ρ : Ty} → ⟦ ρ ⟧ʸ → ⟦ ⟨ ρ ⟩ᴶ ⟧ʸ → Set
R α = LR._R_
 where
  import LogicalRelation Dᵀ₂ ηᵀ κᵀ (Rι α) (Rη α) (Rκ α) as LR

Cor[R] : {ρ : Ty} (t : T ε ρ) (α : ℕᴺ) → R α ⟦ t ⟧ ⟦ t ᴶ ⟧
Cor[R] t α = LR.FTLR t ⋆
 where
  import LogicalRelation Dᵀ₂ ηᵀ κᵀ (Rι α) (Rη α) (Rκ α) as LR

\end{code}

Correctness theorem

The fundamental theorem yields a represented dialogue tree for
every closed term of type `(ι ⇾ ι) ⇾ ι`. The final theorem
compares the standard interpretation of such a term with the
evaluation of its extracted Church-encoded dialogue tree.

\begin{code}

Theorem : (t : T ε ((ι ⇾ ι) ⇾ ι))
        → (α : ℕᴺ) → ⟦ t ⟧ α ≡ ⟦ evalᵀ · dialogue-treeᵀ t ⟧ α
Theorem t α = trans eq₀ (sym eq₁)
 where
  cor : Rι α (⟦ t ⟧ α) (⟦ t ᴶ · Ωᵀ ⟧)
  cor = Cor[R] t α (λ {n} {d} → RΩ α {n} {d})
  d : D
  d = pr₁ cor
  r : d represents ⟦ t ᴶ · Ωᵀ ⟧
  r = pr₁ (pr₂ cor)
  eq₀ : ⟦ t ⟧ α ≡ eval d α
  eq₀ = pr₂ (pr₂ cor)
  eq₁ : ⟦ evalᵀ ⟧ ⟦ dialogue-treeᵀ t ⟧ α ≡ eval d α
  eq₁ = evalᵀ-correct ⋆ d ⟦ t ᴶ · Ωᵀ ⟧ r α

\end{code}
