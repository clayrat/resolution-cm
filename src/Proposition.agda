{-# OPTIONS --safe #-}
module Proposition where

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

-- classical propositional logic
-- https://1lab.dev/Logic.Propositional.Classical.html

infixr 12 _“⇒”_
infixr 11 _“∧”_
infixr 10 _“∨”_
infixl 10 _⨾_
infix 9 _⊢_ _⊨_

data Prp (n : ℕ) : 𝒰 where
  atom        : Fin n → Prp n
  “⊤” “⊥”     : Prp n
  _“∧”_ _“∨”_ : Prp n → Prp n → Prp n
  “¬”_        : Prp n → Prp n

-- context

data Ctx (n : ℕ) : 𝒰 where
  []  : Ctx n
  _⨾_ : Ctx n → Prp n → Ctx n

_++_ : ∀ {n} → Ctx n → Ctx n → Ctx n
γ ++ [] = γ
γ ++ (δ ⨾ p) = (γ ++ δ) ⨾ p

data _∈ᶜ_ {n} (p : Prp n) : Ctx n → 𝒰 where
  here  : ∀ {γ q} → p ＝ q → p ∈ᶜ (γ ⨾ q)
  there : ∀ {γ q} → p ∈ᶜ γ → p ∈ᶜ (γ ⨾ q)

here= : ∀ {n} {γ : Ctx n} {p} → p ∈ᶜ (γ ⨾ p)
here= = here refl

instance
  Membership-Ctx : ∀ {n} → Membership (Prp n) (Ctx n) 0ℓ
  Membership-Ctx ._∈_ = _∈ᶜ_

private variable
  n m : ℕ
  γ δ ζ : Ctx n
  p q r : Prp n

opaque
  _“⇒”_ : ∀ {n} → Prp n → Prp n → Prp n
  p “⇒” q = (“¬” p) “∨” q

“⋀” : Ctx n → Prp n
“⋀” []      = “⊤”
“⋀” (γ ⨾  p) = “⋀” γ “∧” p

_“⇛”_ : Ctx n → Prp n → Prp n
[]      “⇛” p = p
(γ ⨾ q) “⇛” p = γ “⇛” (q “⇒” p)

-- proof calculus

data _⊢_ {n} (γ : Ctx n) : Prp n → 𝒰 where
  hyp       : ∀ {p}     → p ∈ γ
                          -----
                        → γ ⊢ p

  ⊤-intro   :             γ ⊢ “⊤”

  ⊥-elim    : ∀ {p}     → γ ⊢ “⊥”
                          -------
                        → γ ⊢ p

  ∧-intro   : ∀ {p q}   → γ ⊢ p → γ ⊢ q
                          -------------
                        → γ ⊢ p “∧” q

  ∧-elim-l  : ∀ {p q}   → γ ⊢ p “∧” q
                          -----------
                        → γ ⊢ p

  ∧-elim-r  : ∀ {p q}   → γ ⊢ p “∧” q
                          -----------
                        → γ ⊢ q

  ∨-intro-l : ∀ {p q}   → γ ⊢ p
                          -----------
                        → γ ⊢ p “∨” q

  ∨-intro-r : ∀ {p q}   → γ ⊢ q
                          -----------
                        → γ ⊢ p “∨” q

  ∨-elim    : ∀ {p q r} → γ ⊢ p “∨” q → γ ⨾ p ⊢ r → γ ⨾ q ⊢ r
                          -----------------------------------
                        → γ ⊢ r

  ¬-intro   : ∀ {p}     → γ ⨾ p ⊢ “⊥”
                          -----------
                        → γ ⊢ “¬” p

  ¬-elim    : ∀ {p}     → γ ⊢ “¬” p → γ ⊢ p
                          -----------------
                        → γ ⊢ “⊥”

  dneg-elim : ∀ {p}     → γ ⊢ “¬” (“¬” p)
                          ---------------
                        → γ ⊢ p

-- context inclusion / renaming

data Ren {n} : Ctx n → Ctx n → 𝒰 where
  done : Ren [] []
  drop : ∀ {γ δ p} → Ren γ δ → Ren (γ ⨾  p) δ
  keep : ∀ {γ δ p} → Ren γ δ → Ren (γ ⨾  p) (δ ⨾  p)

idrn : Ren γ γ
idrn {γ = []}    = done
idrn {γ = γ ⨾ P} = keep (idrn {γ = γ})

_∘rn_ : Ren δ ζ → Ren γ δ → Ren γ ζ
p      ∘rn done   = p
p      ∘rn drop q = drop (p ∘rn q)
drop p ∘rn keep q = drop (p ∘rn q)
keep p ∘rn keep q = keep (p ∘rn q)

!rn : Ren γ []
!rn {γ = []}    = done
!rn {γ = γ ⨾ x} = drop !rn

π₁-rn : Ren (γ ++ δ) γ
π₁-rn {δ = []}    = idrn
π₁-rn {δ = δ ⨾ P} = drop π₁-rn

π₂-rn : Ren (γ ++ δ) δ
π₂-rn {δ = []}    = !rn
π₂-rn {δ = δ ⨾ P} = keep π₂-rn

rename-hyp : Ren γ δ → p ∈ᶜ δ → p ∈ᶜ γ
rename-hyp (drop rn)  mem        = there (rename-hyp rn mem)
rename-hyp (keep rn) (here e)    = here e
rename-hyp (keep rn) (there mem) = there (rename-hyp rn mem)

rename : Ren γ δ → δ ⊢ p → γ ⊢ p
rename rn (hyp x)        = hyp (rename-hyp rn x)
rename rn  ⊤-intro       = ⊤-intro
rename rn (⊥-elim p)     = ⊥-elim (rename rn p)
rename rn (∧-intro p q)  = ∧-intro (rename rn p) (rename rn q)
rename rn (∧-elim-l p)   = ∧-elim-l (rename rn p)
rename rn (∧-elim-r p)   = ∧-elim-r (rename rn p)
rename rn (∨-intro-l p)  = ∨-intro-l (rename rn p)
rename rn (∨-intro-r p)  = ∨-intro-r (rename rn p)
rename rn (∨-elim p q r) = ∨-elim (rename rn p) (rename (keep rn) q) (rename (keep rn) r)
rename rn (¬-intro p)    = ¬-intro (rename (keep rn) p)
rename rn (¬-elim p q)   = ¬-elim (rename rn p) (rename rn q)
rename rn (dneg-elim p)  = dneg-elim (rename rn p)

-- elementary theorems

dneg-intro : γ ⊢ p → γ ⊢ “¬” (“¬”  p)
dneg-intro p = ¬-intro (¬-elim (hyp here=) (rename (drop idrn) p))

lem : ∀ {n} {γ : Ctx n} (p : Prp n) → γ ⊢ p “∨” (“¬”  p)
lem p =
  dneg-elim                  $
  ¬-intro                    $
  ¬-elim (hyp here=)         $
  ∨-intro-r                  $
  ¬-intro                    $
  ¬-elim (hyp (there here=)) $
  ∨-intro-l (hyp here=)

¬∧-intro-l : γ ⊢ “¬” p → γ ⊢ “¬” (p “∧” q)
¬∧-intro-l p = ¬-intro (¬-elim (rename (drop idrn) p) (∧-elim-l (hyp here=)))

¬∧-intro-r : γ ⊢ “¬” q → γ ⊢ “¬” (p “∧” q)
¬∧-intro-r p = ¬-intro (¬-elim (rename (drop idrn) p) (∧-elim-r (hyp here=)))

¬∧-elim : γ ⊢ “¬” (p “∧” q) → γ ⊢ (“¬” p) “∨” (“¬” q)
¬∧-elim {p} {q} pq =
  ∨-elim (lem p)
    (∨-elim (lem q)
      (⊥-elim
        (¬-elim (rename (drop $ drop idrn) pq)
        (∧-intro (hyp $ there here=) (hyp here=))))
      (∨-intro-r (hyp here=)))
    (∨-intro-l (hyp here=))

¬∨-intro : γ ⊢ “¬” p → γ ⊢ “¬” q → γ ⊢ “¬” (p “∨” q)
¬∨-intro np nq =
  ¬-intro $
  ∨-elim (hyp here=)
    (¬-elim (rename (drop $ drop idrn) np) (hyp here=))
    (¬-elim (rename (drop $ drop idrn) nq) (hyp here=))

-- implication

opaque
  unfolding _“⇒”_

  ⇒-intro : γ ⨾ p ⊢ q → γ ⊢ p “⇒” q
  ⇒-intro {p} pf = ∨-elim (lem p) (∨-intro-r pf) (∨-intro-l (hyp here=))

  ⇒-elim : γ ⊢ p “⇒” q → γ ⊢ p → γ ⊢ q
  ⇒-elim pq p = ∨-elim pq
    (⊥-elim (¬-elim (hyp here=) (rename (drop idrn) p)))
    (hyp here=)

⇒-uncurry : γ ⊢ p “⇒” q → γ ⨾ p ⊢ q
⇒-uncurry p = ⇒-elim (rename (drop idrn) p) (hyp here=)

⇒-flip : γ ⊢ p “⇒” q “⇒” r → γ ⊢ q “⇒” p “⇒” r
⇒-flip p =
  ⇒-intro $ ⇒-intro $
  ⇒-elim
    (⇒-elim (rename (drop $ drop idrn) p) (hyp here=))
    (hyp (there here=))

-- n-ary conjunction

⋀-intro : (∀ {p} → p ∈ γ → δ ⊢ p) → δ ⊢ “⋀” γ
⋀-intro {γ = []}    pfs = ⊤-intro
⋀-intro {γ = γ ⨾ P} pfs = ∧-intro (⋀-intro (pfs ∘ there)) (pfs here=)

⋀-elim : p ∈ γ → δ ⊢ “⋀” γ → δ ⊢ p
⋀-elim {γ = γ ⨾ q} {δ} (here e)  p = ∧-elim-r (subst (λ q → δ ⊢ “⋀” γ “∧” q) (e ⁻¹) p)
⋀-elim                 (there x) p = ⋀-elim x (∧-elim-l p)

-- n-ary implication

⇛-intro : δ ++ γ ⊢ p → δ ⊢ γ “⇛” p
⇛-intro {γ = []}    p = p
⇛-intro {γ = γ ⨾ q} p = ⇛-intro (⇒-intro p)

⇛-uncurry : δ ⊢ γ “⇛” p → δ ++ γ ⊢ p
⇛-uncurry {γ = []}    p = p
⇛-uncurry {γ = γ ⨾ q} p = ⇒-uncurry (⇛-uncurry p)

⇛-elim : δ ⊢ (γ ⨾  p) “⇛” q → δ ⊢ p → δ ⊢ γ “⇛” q
⇛-elim {γ = γ} p q = ⇛-intro (⇒-elim (⇛-uncurry {γ = γ} p) (rename π₁-rn q))

⇛-closed : [] ⊢ γ “⇛” p → γ ⊢ p
⇛-closed {γ = []}    p = p
⇛-closed {γ = γ ⨾ q} p = ⇒-uncurry (⇛-closed p)

-- weakening

data Wk (n : ℕ) : ℕ → 𝒰 where
  done : Wk n n
  weak : ∀ {m} → Wk (suc n) m → Wk n m

¬weaken-suc-zero : ¬ (Wk (suc n) 0)
¬weaken-suc-zero (weak σ) = ¬weaken-suc-zero σ

wk-suc : Wk n m → Wk n (suc m)
wk-suc done     = weak done
wk-suc (weak σ) = weak (wk-suc σ)

!wk : Wk 0 n
!wk {n = zero}  = done
!wk {n = suc n} = wk-suc !wk

inc-prop : Prp n → Prp (suc n)
inc-prop (atom x)  = atom (weaken x)
inc-prop “⊤”       = “⊤”
inc-prop “⊥”       = “⊥”
inc-prop (p “∧” q) = inc-prop p “∧” inc-prop q
inc-prop (p “∨” q) = inc-prop p “∨” inc-prop q
inc-prop (“¬” p)   = “¬” (inc-prop p)

inc-ctx : Ctx n → Ctx (suc n)
inc-ctx []      = []
inc-ctx (γ ⨾  p) = inc-ctx γ ⨾ inc-prop p

inc-atom : p ∈ γ → inc-prop p ∈ᶜ inc-ctx γ
inc-atom (here e)  = here (ap inc-prop e)
inc-atom (there x) = there (inc-atom x)

inc-proof : γ ⊢ p → inc-ctx γ ⊢ inc-prop p
inc-proof (hyp x)        = hyp (inc-atom x)
inc-proof ⊤-intro        = ⊤-intro
inc-proof (⊥-elim p)     = ⊥-elim (inc-proof p)
inc-proof (∧-intro p q)  = ∧-intro (inc-proof p) (inc-proof q)
inc-proof (∧-elim-l p)   = ∧-elim-l (inc-proof p)
inc-proof (∧-elim-r p)   = ∧-elim-r (inc-proof p)
inc-proof (∨-intro-l p)  = ∨-intro-l (inc-proof p)
inc-proof (∨-intro-r p)  = ∨-intro-r (inc-proof p)
inc-proof (∨-elim p q r) = ∨-elim (inc-proof p) (inc-proof q) (inc-proof r)
inc-proof (¬-intro p)    = ¬-intro (inc-proof p)
inc-proof (¬-elim p q)   = ¬-elim (inc-proof p) (inc-proof q)
inc-proof (dneg-elim p)  = dneg-elim (inc-proof p)

wk-atom : Wk n m → Fin n → Fin m
wk-atom  done    x = x
wk-atom (weak σ) x = wk-atom σ (weaken x)

wk-prop : Wk n m → Prp n → Prp m
wk-prop  done    p = p
wk-prop (weak σ) p = wk-prop σ (inc-prop p)

wk-ctx : Wk n m → Ctx n → Ctx m
wk-ctx  done    γ = γ
wk-ctx (weak σ) γ = wk-ctx σ (inc-ctx γ)

wk-proof : (σ : Wk n m) → γ ⊢ p → wk-ctx σ γ ⊢ wk-prop σ p
wk-proof  done    pf = pf
wk-proof (weak σ) pf = wk-proof σ (inc-proof pf)

bump-prop : Prp n → Prp (suc n)
bump-prop (atom x)  = atom (fsuc x)
bump-prop  “⊤”      = “⊤”
bump-prop  “⊥”      = “⊥”
bump-prop (p “∧” q) = bump-prop p “∧” bump-prop q
bump-prop (p “∨” q) = bump-prop p “∨” bump-prop q
bump-prop (“¬” p)   = “¬” bump-prop p

bump-ctx : Ctx n → Ctx (suc n)
bump-ctx []       = []
bump-ctx (γ ⨾  p) = bump-ctx γ ⨾ bump-prop p

bump-atom : p ∈ γ → bump-prop p ∈ᶜ bump-ctx γ
bump-atom (here e)  = here (ap bump-prop e)
bump-atom (there p) = there (bump-atom p)

bump-proof : γ ⊢ p → bump-ctx γ ⊢ bump-prop p
bump-proof (hyp x)        = hyp (bump-atom x)
bump-proof  ⊤-intro       = ⊤-intro
bump-proof (⊥-elim p)     = ⊥-elim (bump-proof p)
bump-proof (∧-intro p q)  = ∧-intro (bump-proof p) (bump-proof q)
bump-proof (∧-elim-l p)   = ∧-elim-l (bump-proof p)
bump-proof (∧-elim-r p)   = ∧-elim-r (bump-proof p)
bump-proof (∨-intro-l p)  = ∨-intro-l (bump-proof p)
bump-proof (∨-intro-r p)  = ∨-intro-r (bump-proof p)
bump-proof (∨-elim p q r) = ∨-elim (bump-proof p) (bump-proof q) (bump-proof r)
bump-proof (¬-intro p)    = ¬-intro (bump-proof p)
bump-proof (¬-elim p q)   = ¬-elim (bump-proof p) (bump-proof q)
bump-proof (dneg-elim p)  = dneg-elim (bump-proof p)

shift-atom : Wk n m → Fin n → Fin m
shift-atom  done    f = f
shift-atom (weak σ) f = shift-atom σ (fsuc f)

shift-prop : Wk n m → Prp n → Prp m
shift-prop  done    p = p
shift-prop (weak σ) p = shift-prop σ (bump-prop p)

shift-ctx : Wk n m → Ctx n → Ctx m
shift-ctx  done    γ = γ
shift-ctx (weak σ) γ = shift-ctx σ (bump-ctx γ)

shift-ctx-[] : (σ : Wk n m) → shift-ctx σ [] ＝ []
shift-ctx-[]  done    = refl
shift-ctx-[] (weak σ) = shift-ctx-[] σ

shift-ctx-⨾ : (σ : Wk n m) (γ : Ctx n) (p : Prp n)
            → shift-ctx σ (γ ⨾  p) ＝ shift-ctx σ γ ⨾ shift-prop σ p
shift-ctx-⨾  done    γ p = refl
shift-ctx-⨾ (weak σ) γ p = shift-ctx-⨾ σ (bump-ctx γ) (bump-prop  p)

shift-prop-“¬” : (σ : Wk n m) (p : Prp n)
               → shift-prop σ (“¬” p) ＝ “¬” (shift-prop σ p)
shift-prop-“¬” done     p = refl
shift-prop-“¬” (weak σ) p = shift-prop-“¬” σ (bump-prop p)

-- semantics

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
