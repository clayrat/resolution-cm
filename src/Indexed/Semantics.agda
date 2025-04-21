{-# OPTIONS --safe #-}
module Indexed.Semantics where

open import Prelude

open import Data.Empty
open import Data.Reflects as Reflects
open import Data.Dec as Dec
open import Data.Bool as Bool
open import Data.List hiding (_++_ ; drop)
open import Data.Fin as Fin using (Fin; fzero; fsuc; elim)
open import Data.Fin.Operations
open import Data.Nat
open import Data.Nat.Order.Inductive  -- inherited from Data.Fin.Instances.FromNat
open import Data.Sum

open import Indexed.Proposition

-- semantics

infix 9 _⊨_

private variable
  n m : ℕ
  γ δ ζ : Ctx n
  p q r : Prp n

Val : ℕ → 𝒰
Val n = Fin n → Bool

emp-val : Val 0
emp-val ()

sem-prop : ∀ {n} → Prp n → Val n → Bool
sem-prop (atom x)  v = v x
sem-prop “⊤”       v = true
sem-prop “⊥”       v = false
sem-prop (p “∧” q) v = (sem-prop p v) and (sem-prop q v)
sem-prop (p “∨” q) v = (sem-prop p v) or (sem-prop q v)
sem-prop (“¬” p)   v = not (sem-prop p v)

sem-ctx : ∀ {n} → Ctx n → Val n → Bool
sem-ctx γ = sem-prop (“⋀” γ)

instance
  ⟦⟧-Prp : ∀ {n} → ⟦⟧-notation (Prp n)
  ⟦⟧-Prp {n} = brackets (Val n → Bool) sem-prop

  ⟦⟧-Ctx : ∀ {n} → ⟦⟧-notation (Ctx n)
  ⟦⟧-Ctx {n} = brackets (Val n → Bool) sem-ctx

  Number-Prp : ∀ {n} → From-ℕ (Prp n)
  Number-Prp {n} .From-ℕ.Constraint = _< n
  Number-Prp     .From-ℕ.fromNat m  = atom (from-ℕ m)

opaque
  unfolding _“⇒”_

  ⇒-sem : ∀ {n} {p q : Prp n}
        → ∀ (v : Val n) → ⟦ p “⇒” q ⟧ v ＝ (⟦ p ⟧ v) implies (⟦ q ⟧ v)
  ⇒-sem {p} {q} v =
    implies-not-or (⟦ p ⟧ v) (⟦ q ⟧ v)

⇛-sem : ∀ {n} {p : Prp n} {v : Val n}
      → (γ : Ctx n)
      → ⟦ γ “⇛” p ⟧ v ＝ ⟦ γ ⟧ v implies ⟦ p ⟧ v
⇛-sem {p} {v} [] = implies-true-l (⟦ p ⟧ v) ⁻¹
⇛-sem {p} {v} (γ ⨾ q) =
    ⇛-sem {p = q “⇒” p} γ
  ∙ ap² _implies_ refl (⇒-sem v)
  ∙ implies-curry (⟦ γ ⟧ v) (⟦ q ⟧ v) (⟦ p ⟧ v)

reflects-⇛-sem : ∀ {n} {γ : Ctx n} {p : Prp n} {v : Val n}
               → Reflects (⌞ ⟦ γ ⟧ v ⌟ → ⌞ ⟦ p ⟧ v ⌟) (⟦ γ “⇛” p ⟧ v)
reflects-⇛-sem {γ} {p} {v} =
  subst (Reflects (⌞ ⟦ γ ⟧ v ⌟ → ⌞ ⟦ p ⟧ v ⌟))
        (⇛-sem γ ⁻¹)
        reflects-implies

-- semantic entailment

_⊨_ : ∀ {n} → Ctx n → Prp n → Type
_⊨_ {n} γ p = (v : Val n) → ⌞ ⟦ γ ⟧ v ⌟ → ⌞ ⟦ p ⟧ v ⌟

⇛-valid : (γ : Ctx n) (p : Prp n)
        → γ ⊨ p → [] ⊨ (γ “⇛” p)
⇛-valid {n} γ p vd v _ =
  true→so! ⦃ reflects-⇛-sem {γ = γ} ⦄ (vd v)

-- soundness

hyp-sound : ∀ {n} {γ : Ctx n} {p : Prp n} → p ∈ γ → γ ⊨ p
hyp-sound {γ = γ ⨾ q} (here e)  v hp =
  and-so-r (subst (λ q → ⌞ ⟦ “⋀” γ ⟧ v and ⟦ q ⟧ v ⌟) (e ⁻¹) hp)
hyp-sound             (there m) v hp = hyp-sound m v (and-so-l hp)

sound : γ ⊢ p → γ ⊨ p
sound (hyp x)             v hp = hyp-sound x v hp
sound  ⊤-intro            v hp = oh
sound (⊥-elim e)          v hp = false! $ sound e v hp
sound (∧-intro p q)       v hp = sound p v hp × sound q v hp
sound (∧-elim-l p)        v hp = and-so-l $ sound p v hp
sound (∧-elim-r p)        v hp = and-so-r $ sound p v hp
sound (∨-intro-l p)       v hp = or-so-l $ sound p v hp
sound (∨-intro-r p)       v hp = or-so-r $ sound p v hp
sound (∨-elim pq l r)     v hp =
  [ sound l v ∘ and-so-intro hp
  , sound r v ∘ and-so-intro hp ]ᵤ $
  or-so-elim $
  sound pq v hp
sound (¬-intro {p} np)    v hp =
  Dec.rec
    (λ sp → false! (sound np v (and-so-intro hp sp)))
    not-so
    (oh? (⟦ p ⟧ v))
sound (¬-elim np yp)      v hp =
  absurd (so-not (sound np v hp) (sound yp v hp))
sound (dneg-elim {p} nnp) v hp =
  subst So (not-invol (⟦ p ⟧ v)) $
  sound nnp v hp

-- completeness

tabulate : Val n → Ctx n
tabulate {n = zero}  v = []
tabulate {n = suc n} v =
  bump-ctx (tabulate (v ∘ fsuc)) ⨾ (if v 0 then 0 else “¬” 0)

tabulate-atom-true : (x : Fin n) (v : Val n)
                   → ⌞ v x ⌟ → tabulate v ⊢ atom x
tabulate-atom-true =
  Fin.elim
    (λ {n} q → (v : Val n) → ⌞ v q ⌟ → tabulate v ⊢ atom q)
    (λ v sv → hyp $ here $ if-true sv ⁻¹)
    (λ ih v sv → rename (drop idrn) $ bump-proof $ ih (v ∘ fsuc) sv)

tabulate-atom-false : (x : Fin n) (v : Val n)
                    → ⌞ not (v x) ⌟ → tabulate v ⊢ “¬” atom x
tabulate-atom-false =
  Fin.elim
    (λ {n} q → (v : Val n) → ⌞ not (v q) ⌟ → tabulate v ⊢ “¬” atom q)
    (λ v snv → hyp $ here $ if-false snv ⁻¹)
    (λ ih v snv → rename (drop idrn) $ bump-proof $ ih (v ∘ fsuc) snv)

mutual
  tabulate-true : (p : Prp n) (v : Val n)
                → ⌞ ⟦ p ⟧ v ⌟ → tabulate v ⊢ p
  tabulate-true (atom x)  v pt = tabulate-atom-true x v pt
  tabulate-true  “⊤”      v pt = ⊤-intro
  tabulate-true (p “∧” q) v pt =
    ∧-intro (tabulate-true p v (and-so-l pt))
            (tabulate-true q v (and-so-r pt))
  tabulate-true (p “∨” q) v pt =
    [ ∨-intro-l ∘ tabulate-true p v
    , ∨-intro-r ∘ tabulate-true q v
    ]ᵤ $
    or-so-elim pt
  tabulate-true (“¬” p)   v pt = tabulate-false p v pt

  tabulate-false : (p : Prp n) (v : Val n)
                 → ⌞ not (⟦ p ⟧ v) ⌟ → tabulate v ⊢ “¬” p
  tabulate-false (atom x)  v pf = tabulate-atom-false x v pf
  tabulate-false  “⊥”      v pf = ¬-intro (hyp here=)
  tabulate-false (p “∧” q) v pf =
    [ ¬∧-intro-l ∘ tabulate-false p v
    , ¬∧-intro-r ∘ tabulate-false q v
    ]ᵤ $
    or-so-elim {x = not (⟦ p ⟧ v)} $
    subst So (not-and _ (⟦ q ⟧ v)) $ pf
  tabulate-false (p “∨” q) v pf =
    ¬∨-intro (tabulate-false p v $ not-so $ contra or-so-l $ so-not pf)
             (tabulate-false q v $ not-so $ contra or-so-r $ so-not pf)
  tabulate-false (“¬” p)   v pf =
    dneg-intro $
    tabulate-true p v $
    subst So (not-invol (⟦ p ⟧ v)) $ pf

tabulate-complete : ∀ {m n} (p : Prp n)
                  → (σ : Wk m n) (v : Val m)
                  → [] ⊨ p → shift-ctx σ (tabulate v) ⊢ p
tabulate-complete p  done    v pta = tabulate-true p v (pta v oh)
tabulate-complete p (weak σ) v pta =
  ∨-elim
    (lem (shift-prop σ (atom 0)))
    (subst (_⊢ p)
           (shift-ctx-⨾ σ _ _) $
     tabulate-complete p σ (v [ 0 ≔ true ]) pta)
    (subst (_⊢ p)
           (  shift-ctx-⨾ σ _ _
            ∙ ap² _⨾_ refl (shift-prop-“¬” σ (atom 0))) $
     tabulate-complete p σ (v [ 0 ≔ false ]) pta)

taut-complete : (p : Prp n) → [] ⊨ p → [] ⊢ p
taut-complete p pta =
  subst (_⊢ p) (shift-ctx-[] !wk) $
  tabulate-complete p !wk emp-val pta

complete : γ ⊨ p → γ ⊢ p
complete {γ} {p} =
  ⇛-closed ∘ taut-complete (γ “⇛” p) ∘ ⇛-valid γ p
