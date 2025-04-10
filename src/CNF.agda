{-# OPTIONS --safe #-}
module CNF where

open import Prelude
open import Meta.Effect
open import Meta.Effect.Map.Lawful

open import Data.Empty hiding (_≠_)
open import Data.Dec as Dec
open import Data.Bool as Bool
open import Data.Fin as Fin
open import Data.Fin.Operations
open import Data.List as List
open import Data.List.Operations.Properties

open import Proposition

-- conjunctive normal forms
-- https://1lab.dev/Logic.Propositional.Classical.CNF.html

data Lit (n : ℕ) : Type where
  pos : Fin n → Lit n
  neg : Fin n → Lit n

-- TODO try LFSet

Clause : (n : ℕ) → 𝒰
Clause n = List (Lit n)

CNF : (n : ℕ) → 𝒰
CNF n = List (Clause n)

private variable
  n : ℕ
  γ : Ctx n
  p : Prp n

pos≠neg : ∀ {x y : Fin n} → pos x ＝ neg y → ⊥
pos≠neg {n = n} p = subst is-pos p tt where
  is-pos : Lit n → Type
  is-pos (pos x) = ⊤
  is-pos (neg x) = ⊥

lit-var : Lit n → Fin n
lit-var (pos x) = x
lit-var (neg x) = x

lit-val : Lit n → Bool
lit-val (pos _) = true
lit-val (neg _) = false

pos-inj : {x y : Fin n} → pos x ＝ pos y → x ＝ y
pos-inj p = ap lit-var p

neg-inj : {x y : Fin n} → neg x ＝ neg y → x ＝ y
neg-inj p = ap lit-var p

instance
  Discrete-Lit : is-discrete (Lit n)
  Discrete-Lit {x = pos x} {y = pos y} = Dec.dmap (ap pos) (contra pos-inj) (x ≟ y)
  Discrete-Lit {x = pos x} {y = neg y} = no pos≠neg
  Discrete-Lit {x = neg x} {y = pos y} = no (pos≠neg ∘ sym)
  Discrete-Lit {x = neg x} {y = neg y} = Dec.dmap (ap neg) (contra neg-inj) (x ≟ y)

avoid-lit : (i : Fin (suc n)) (x : Lit (suc n)) → i ≠ lit-var x → Lit n
avoid-lit i (pos x) p = pos (avoid i x p)
avoid-lit i (neg x) p = neg (avoid i x p)

-- semantics

pos-sem : Lit n → Val n → Bool
pos-sem (pos x) v = v x
pos-sem (neg x) v = not (v x)

clause-sem : Clause n → Val n → Bool
clause-sem ps v = any (λ a → pos-sem a v) ps

cnf-sem : CNF n → Val n → Bool
cnf-sem ps v = all (λ d → clause-sem d v) ps

instance
  ⟦⟧-Lit : ⟦⟧-notation (Lit n)
  ⟦⟧-Lit {n} = brackets (Val n → Bool) pos-sem

  ⟦⟧-Clause : ⟦⟧-notation (Clause n)
  ⟦⟧-Clause {n} = brackets (Val n → Bool) clause-sem

  ⟦⟧-CNF : ⟦⟧-notation (CNF n)
  ⟦⟧-CNF {n} = brackets (Val n → Bool) cnf-sem

-- soundness

cnf-atom : Fin n → CNF n
cnf-atom x = (pos x ∷ []) ∷ []

⊤cnf : CNF n
⊤cnf = []

⊥cnf : CNF n
⊥cnf = [] ∷ []

_∧cnf_ : CNF n → CNF n → CNF n
xs ∧cnf ys = xs List.++ ys

cnf-distrib : Clause n → CNF n → CNF n
cnf-distrib p q = map (p List.++_) q

_∨cnf_ : CNF n → CNF n → CNF n
[]       ∨cnf q = []
(p ∷ ps) ∨cnf q = cnf-distrib p q ∧cnf (ps ∨cnf q)

¬lit : Lit n → Lit n
¬lit (pos x) = neg x
¬lit (neg x) = pos x

¬clause : Clause n → CNF n
¬clause = map (λ a → ¬lit a ∷ [])

¬cnf : CNF n → CNF n
¬cnf []      = ⊥cnf
¬cnf (p ∷ q) = ¬clause p ∨cnf ¬cnf q

literal-eq-negate : ∀ (x y : Lit n) → x ≠ y → lit-var x ＝ lit-var y → x ＝ ¬lit y
literal-eq-negate (pos x) (pos y) x≠y p = absurd (x≠y (ap pos p))
literal-eq-negate (pos x) (neg y) x≠y p = ap pos p
literal-eq-negate (neg x) (pos y) x≠y p = ap neg p
literal-eq-negate (neg x) (neg y) x≠y p = absurd (x≠y (ap neg p))

literal-sat-val : ∀ (x : Lit n) → (v : Val n) → ⌞ ⟦ x ⟧ v ⌟ → v (lit-var x) ＝ lit-val x
literal-sat-val (pos x) v xt = so≃is-true $ xt
literal-sat-val (neg x) v xt = ¬so≃is-false $ so-not xt

cnf-atom-sound : (x : Fin n) (v : Val n) → ⟦ cnf-atom x ⟧ v ＝ v x
cnf-atom-sound x v = and-id-r _ ∙ or-id-r _

⊥cnf-sound : (v : Val n) → ⌞ not (⟦ ⊥cnf ⟧ v) ⌟
⊥cnf-sound v = oh

⊤cnf-sound : (v : Val n) → ⌞ ⟦ ⊤cnf ⟧ v ⌟
⊤cnf-sound v = oh

∧cnf-sound : (ϕ ψ : CNF n) → (v : Val n)
           → ⟦ ϕ ∧cnf ψ ⟧ v ＝ (⟦ ϕ ⟧ v) and (⟦ ψ ⟧ v)
∧cnf-sound ϕ ψ v =
  all?-++ {p = λ d → clause-sem d v} {xs = ϕ} {ys = ψ}

cnf-distrib-sound : (ϕ : Clause n) (ψ : CNF n)
                  → (v : Val n)
                  → ⟦ cnf-distrib ϕ ψ ⟧ v ＝ (⟦ ϕ ⟧ v) or (⟦ ψ ⟧ v)
cnf-distrib-sound  []     ψ v =
  ap (all (λ d → clause-sem d v)) (happly map-pres-id ψ)
cnf-distrib-sound (p ∷ ϕ) ψ v =
  all (λ d → ⟦ d ⟧ v) (map (λ ys → p ∷ (ϕ List.++ ys)) ψ)   ~⟨ all?-map {xs = ψ} ⟩
  all (λ d → ⟦ p ∷ (ϕ List.++ d) ⟧ v) ψ                     ~⟨ ap (λ d → all d ψ) (fun-ext λ d → any?-++ {xs = p ∷ ϕ}) ⟩
  all (λ d → (⟦ p ∷ ϕ ⟧ v) or (⟦ d ⟧ v)) ψ                  ~⟨ all?-or {xs = ψ} ⟩
  (⟦ p ∷ ϕ ⟧ v) or (⟦ ψ ⟧ v)                                ∎

∨cnf-sound : (ϕ ψ : CNF n)
           → (v : Val n)
           → ⟦ ϕ ∨cnf ψ ⟧ v ＝ (⟦ ϕ ⟧ v) or (⟦ ψ ⟧ v)
∨cnf-sound  []      ψ v = refl
∨cnf-sound (p ∷ ϕ) ψ v =
  ⟦ (p ∷ ϕ) ∨cnf ψ ⟧ v                                     ~⟨ all?-++ {xs = cnf-distrib p ψ} ⟩
  (⟦ cnf-distrib p ψ ⟧ v) and (⟦ ϕ ∨cnf ψ ⟧ v)             ~⟨ ap² _and_ (cnf-distrib-sound p ψ v) (∨cnf-sound ϕ ψ v) ⟩
  ((⟦ p ⟧ v) or (⟦ ψ ⟧ v)) and ((⟦ ϕ ⟧ v) or (⟦ ψ ⟧ v))    ~⟨ or-distrib-and-r (⟦ p ⟧ v) _ _ ⟨
  ⟦ p ∷ ϕ ⟧ v or ⟦ ψ ⟧ v                                   ∎

¬lit-sound : (a : Lit n) (v : Val n)
           → ⟦ ¬lit a ⟧ v ＝ not (⟦ a ⟧ v)
¬lit-sound (pos x) v = refl
¬lit-sound (neg x) v = not-invol (v x) ⁻¹

¬clause-sound : (ϕ : Clause n) (v : Val n)
              → ⟦ ¬clause ϕ ⟧ v ＝ not (⟦ ϕ ⟧ v)
¬clause-sound ϕ v =
  all (λ d → ⟦ d ⟧ v) (map (λ a → ¬lit a ∷ []) ϕ)  ~⟨ all?-map {xs = ϕ} ⟩
  all (λ a → (⟦ ¬lit a ⟧ v) or false) ϕ            ~⟨ ap (λ a → all a ϕ) (fun-ext λ a → or-id-r (⟦ ¬lit a ⟧ v)) ⟩
  all (λ a → ⟦ ¬lit a ⟧ v) ϕ                       ~⟨ ap (λ a → all a ϕ) (fun-ext λ a → ¬lit-sound a v) ⟩
  all (λ a → not (⟦ a ⟧ v)) ϕ                      ~⟨ not-any? {xs = ϕ} ⟨
  not (⟦ ϕ ⟧ v)                                    ∎

¬cnf-sound : (ϕ : CNF n) (v : Val n)
           → ⟦ ¬cnf ϕ ⟧ v ＝ not (⟦ ϕ ⟧ v)
¬cnf-sound  []      v = refl
¬cnf-sound (p ∷ ϕ) v =
  ⟦ (¬clause p ∨cnf ¬cnf ϕ) ⟧ v        ~⟨ ∨cnf-sound (¬clause p) (¬cnf ϕ) v ⟩
  (⟦ ¬clause p ⟧ v) or (⟦ ¬cnf ϕ ⟧ v)  ~⟨ ap² _or_ (¬clause-sound p v) (¬cnf-sound ϕ v) ⟩
  (not (⟦ p ⟧ v)) or (not (⟦ ϕ ⟧ v))   ~⟨ not-and (⟦ p ⟧ v) _ ⟨
  not (⟦ p ∷ ϕ ⟧ v)                    ∎

-- naive algorithm

to-cnf : Prp n → CNF n
to-cnf (atom x)  = cnf-atom x
to-cnf “⊤”       = ⊤cnf
to-cnf “⊥”       = ⊥cnf
to-cnf (p “∧” q) = to-cnf p ∧cnf to-cnf q
to-cnf (p “∨” q) = to-cnf p ∨cnf to-cnf q
to-cnf (“¬” p)   = ¬cnf (to-cnf p)

to-cnf-sound : (p : Prp n) (v : Val n)
             → ⟦ to-cnf p ⟧ v ＝ ⟦ p ⟧ v
to-cnf-sound (atom x)  v = cnf-atom-sound x v
to-cnf-sound  “⊤”      v = refl
to-cnf-sound  “⊥”      v = refl
to-cnf-sound (p “∧” q) v =
    ∧cnf-sound (to-cnf p) (to-cnf q) v
  ∙ ap² _and_ (to-cnf-sound p v) (to-cnf-sound q v)
to-cnf-sound (p “∨” q) v =
    ∨cnf-sound (to-cnf p) (to-cnf q) v
  ∙ ap² _or_ (to-cnf-sound p v) (to-cnf-sound q v)
to-cnf-sound (“¬” p)   v =
    ¬cnf-sound (to-cnf p) v
  ∙ ap not (to-cnf-sound p v)

-- quotation

quote-pos : Lit n → Prp n
quote-pos (pos x) = atom x
quote-pos (neg x) = “¬” (atom x)

quote-clause : Clause n → Prp n
quote-clause []      = “⊥”
quote-clause (x ∷ ϕ) = quote-pos x “∨” quote-clause ϕ

quote-cnf : CNF n → Prp n
quote-cnf []       = “⊤”
quote-cnf (ϕ ∷ ψ) = quote-clause ϕ “∧” quote-cnf ψ

quote-pos-sound : (x : Lit n)
                → (v : Val n) → ⟦ x ⟧ v ＝ ⟦ quote-pos x ⟧ v
quote-pos-sound (pos x) v = refl
quote-pos-sound (neg x) v = refl

quote-clause-sound : (ϕ : Clause n)
                   → (v : Val n) → ⟦ ϕ ⟧ v ＝ ⟦ quote-clause ϕ ⟧ v
quote-clause-sound []      v = refl
quote-clause-sound (p ∷ ϕ) v = ap² _or_ (quote-pos-sound p v) (quote-clause-sound ϕ v)

quote-cnf-sound : (ψ : CNF n) → (v : Val n) → ⟦ ψ ⟧ v ＝ ⟦ quote-cnf ψ ⟧ v
quote-cnf-sound []      v = refl
quote-cnf-sound (ϕ ∷ ψ) v = ap² _and_ (quote-clause-sound ϕ v) (quote-cnf-sound ψ v)
