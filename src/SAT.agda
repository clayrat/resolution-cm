{-# OPTIONS --safe #-}
module SAT where

open import Prelude
open import Meta.Effect

open import Data.Empty hiding (_≠_)
open import Data.Bool as Bool
open import Data.Reflects as Reflects
open import Data.Reflects.Sigma as ReflectsΣ
open import Data.Dec as Dec
open import Data.Dec.Sigma as DecΣ
open import Data.Fin as Fin
open import Data.Fin.Operations
open import Data.Fin.Operations.Properties
open import Data.Sum as Sum
open import Data.Maybe as Maybe
open import Data.List as List
open import Data.List.Correspondences.Unary.Any

open import Proposition
open import CNF

-- SAT solving
-- https://1lab.dev/Logic.Propositional.Classical.SAT.html

private variable
  n : ℕ
  γ : Ctx n
  p : Prp n

delete-literal : Fin (suc n) → Clause (suc n)
               → Clause n
delete-literal {n = zero}  _ _       = []
delete-literal {n = suc n} _ []      = []
delete-literal {n = suc n} f (p ∷ ϕ) =
  Dec.rec
    (λ _   → delete-literal f ϕ)
    (λ f≠p → avoid-lit f p f≠p ∷ delete-literal f ϕ)
    (f ≟ lit-var p)

unit-propagate : Lit (suc n) → CNF (suc n) → CNF n
unit-propagate x []      = []
unit-propagate x (ϕ ∷ ψ) =
  if has x ϕ
    then unit-propagate x ψ
    else delete-literal (lit-var x) ϕ ∷ unit-propagate x ψ

-- correctness

avoid-lit-insert : (x y : Lit (suc n)) (x≠y : lit-var x ≠ lit-var y) (v : Val n)
                 → ⟦ y ⟧ (v [ lit-var x ≔ lit-val x ]) ＝ ⟦ avoid-lit (lit-var x) y x≠y ⟧ v
avoid-lit-insert x (pos y) x≠y v =
  avoid-insert v (lit-var x) (lit-val x) y x≠y
avoid-lit-insert x (neg y) x≠y v =
  ap not (avoid-insert v (lit-var x) (lit-val x) y x≠y)

-- TODO hacky
lit-assign-neg-false : (x : Lit (suc n)) (v : Val n)
                     → (⟦ x ⟧ (v [ lit-var (¬lit x) ≔ lit-val (¬lit x) ])) ＝ false
lit-assign-neg-false (pos x) v =
 insert-lookup v x false
lit-assign-neg-false (neg x) v =
  ap not (insert-lookup v x true)

lit-assign-true : (x : Lit (suc n)) (v : Val n)
                → (⟦ x ⟧ (v [ lit-var x ≔ lit-val x ])) ＝ true
lit-assign-true (pos x) v =
  insert-lookup v x true
lit-assign-true (neg x) v =
  ap not (insert-lookup v x false)

delete-literal-sound : (x : Lit (suc n)) (ϕ : Clause (suc n))
                     → x ∉ ϕ
                     → (v : Val n)
                     → ⟦ ϕ ⟧ (v [ lit-var x ≔ lit-val x ]) ＝ ⟦ delete-literal (lit-var x) ϕ ⟧ v
delete-literal-sound {n = zero}   x            []              x∉ϕ v = refl
delete-literal-sound {n = zero}  (pos f)      (pos g ∷ ϕ)      x∉ϕ v with fin-view f | fin-view g
delete-literal-sound {n = zero}  (pos .fzero) (pos .fzero ∷ ϕ) x∉ϕ v | zero | zero =
  absurd (x∉ϕ (here refl))
delete-literal-sound {n = zero}  (pos f)      (neg g ∷ ϕ)      x∉ϕ v with fin-view f | fin-view g
delete-literal-sound {n = zero}  (pos .fzero) (neg .fzero ∷ ϕ) x∉ϕ v | zero | zero =
  delete-literal-sound (pos fzero) ϕ (x∉ϕ ∘ there) v
delete-literal-sound {n = zero}  (neg f)      (pos g ∷ ϕ)      x∉ϕ v with fin-view f | fin-view g
delete-literal-sound {n = zero}  (neg .fzero) (pos .fzero ∷ ϕ) x∉ϕ v | zero | zero =
  delete-literal-sound (neg fzero) ϕ (x∉ϕ ∘ there) v
delete-literal-sound {n = zero}  (neg f)      (neg g ∷ ϕ)      x∉ϕ v with fin-view f | fin-view g
delete-literal-sound {n = zero}  (neg .fzero) (neg .fzero ∷ ϕ) x∉ϕ v | zero | zero =
  absurd (x∉ϕ (here refl))
delete-literal-sound {n = suc n}  x            []              x∉ϕ v = refl
delete-literal-sound {n = suc n}  x           (y ∷ ϕ)          x∉ϕ v with lit-var x ≟ lit-var y
... | yes e =
    ap² _or_
      (  ap (λ q → ⟦ y ⟧ (v [ lit-var q ≔ lit-val q ]))
            (literal-eq-negate x y (x∉ϕ ∘ here) e)
       ∙ lit-assign-neg-false y v)
    refl
  ∙ delete-literal-sound x ϕ (x∉ϕ ∘ there) v
... | no ne =
  ap² _or_
    (avoid-lit-insert x y ne v)
    (delete-literal-sound x ϕ (x∉ϕ ∘ there) v)

unit-propagate-sound : (x : Lit (suc n)) (ψ : CNF (suc n)) (v : Val n)
                     → ⟦ ψ ⟧ (v [ lit-var x ≔ lit-val x ]) ＝ ⟦ unit-propagate x ψ ⟧ v
unit-propagate-sound x []      v = refl
unit-propagate-sound x (ϕ ∷ ψ) v =
  Dec.elim
    {C = λ q →    ⟦ ϕ ∷ ψ ⟧ (v [ lit-var x ≔ lit-val x ])
               ＝ ⟦ if ⌊ q ⌋
                     then unit-propagate x ψ
                     else delete-literal (lit-var x) ϕ ∷ unit-propagate x ψ ⟧ v }
    (λ x∈ϕ →
        ap² _and_
          (so≃is-true $
           true→so! ⦃ Reflects-any-bool ⦄ $
           ∈→Any x∈ϕ (so≃is-true ⁻¹ $ lit-assign-true x v))
          (unit-propagate-sound x ψ v))
    (λ x∉ϕ → ap² _and_
               (delete-literal-sound x ϕ x∉ϕ v)
               (unit-propagate-sound x ψ v))
    (x ∈? ϕ)

unit-propagate-complete : (x : Lit (suc n)) (ψ : CNF (suc n)) (v : Val (suc n))
                        → ⌞ ⟦ x ⟧ v ⌟
                        → ⟦ ψ ⟧ v ＝ ⟦ unit-propagate x ψ ⟧ (delete v (lit-var x))
unit-propagate-complete x ψ v xt =
    ap ⟦ ψ ⟧ (fun-ext (insert-delete v (lit-var x) (lit-val x) (literal-sat-val x v xt)) ⁻¹)
  ∙ unit-propagate-sound x ψ (delete v (lit-var x))

has-unit-clause? : CNF n → Maybe (Lit n)
has-unit-clause?  []                = nothing
has-unit-clause? ([]           ∷ ψ) = has-unit-clause? ψ
has-unit-clause? ((x     ∷ []) ∷ ψ) = just x
has-unit-clause? ((x ∷ y ∷ ϕ)  ∷ ψ) = has-unit-clause? ψ

reflects-has-unit-clause : (ψ : CNF n)
                         → ReflectsΣ (λ x → (x ∷ []) ∈ ψ) (has-unit-clause? ψ)
reflects-has-unit-clause [] =
  ofⁿ (λ l l∈ → false! l∈)
reflects-has-unit-clause ([] ∷ ψ) =
  ReflectsΣ.dmap
    (λ x → there)
    (λ x → contra ([ false! , id ]ᵤ ∘ any-uncons))
    (reflects-has-unit-clause ψ)
reflects-has-unit-clause ((x ∷ []) ∷ ψ) =
  ofʲ x (here refl)
reflects-has-unit-clause ((x ∷ y ∷ f) ∷ ψ) =
  ReflectsΣ.dmap
    (λ x → there)
    (λ x → contra ([ false! ∘ ∷-tail-inj , id ]ᵤ ∘ any-uncons))
    (reflects-has-unit-clause ψ)

dec-has-unit-clause : (ψ : CNF n)
                    → DecΣ λ (x : Lit n) → (x ∷ []) ∈ ψ
dec-has-unit-clause ψ .doesm  = has-unit-clause? ψ
dec-has-unit-clause ψ .proofm = reflects-has-unit-clause ψ

unit-clause-sat : (x : Lit n) (ψ : CNF n)
                → (x ∷ []) ∈ ψ
                → (v : Val n) → ⌞ ⟦ ψ ⟧ v ⌟ → ⌞ ⟦ x ⟧ v ⌟   -- a variant of semantic entailment?
unit-clause-sat x (ϕ ∷ ψ) (here  xe) v ψv =
  subst So (or-id-r _) $
  subst (λ q → ⌞ ⟦ q ⟧ v ⌟) (xe ⁻¹) $
  and-so-l ψv
unit-clause-sat x (ϕ ∷ ψ) (there xu) v ψv =
  unit-clause-sat x ψ xu v (and-so-r ψv)

¬empty-clause-sat : (ϕ : Clause 0) (v : Val 0) → ⌞ not (⟦ ϕ ⟧ v) ⌟
¬empty-clause-sat []           _ = oh
¬empty-clause-sat (pos () ∷ ϕ) v
¬empty-clause-sat (neg () ∷ ϕ) v

val-add : Lit (suc n) → Val n → Val (suc n)
val-add x v = v [ lit-var x ≔ lit-val x ]

unit-propagate-sat-add : (x : Lit (suc n)) (ψ : CNF (suc n))
                       → (v : Val n) → ⌞ ⟦ unit-propagate x ψ ⟧ v ⌟
                       → ⌞ ⟦ ψ ⟧ (val-add x v) ⌟
unit-propagate-sat-add x ψ v vs =
  subst So (unit-propagate-sound x ψ v ⁻¹) vs

val-rem : Lit (suc n) → Val (suc n) → Val n
val-rem x v = delete v (lit-var x)

unit-propagate-sat-rem : (x : Lit (suc n)) (ψ : CNF (suc n))
                       → (v : Val (suc n)) → ⌞ ⟦ ψ ⟧ v ⌟ → ⌞ ⟦ x ⟧ v ⌟
                       → ⌞ ⟦ unit-propagate x ψ ⟧ (val-rem x v) ⌟
unit-propagate-sat-rem x ψ v vs xs =
  subst So (unit-propagate-complete x ψ v xs) vs

cnf-sat? : CNF n → Maybe (Val n)
cnf-sat? {n = zero}   []     = just emp-val
cnf-sat? {n = zero}  (_ ∷ _) = nothing
cnf-sat? {n = suc n}  ψ      =
  Maybe.rec
    ([ val-add (pos 0) , val-add (neg 0) ]ᵤ
     <$> (    (cnf-sat? (unit-propagate (pos 0) ψ))
          <+> (cnf-sat? (unit-propagate (neg 0) ψ))))
    (λ x → val-add x <$> cnf-sat? (unit-propagate x ψ))
    (has-unit-clause? ψ)

reflects-cnf-sat : (ψ : CNF n) → ReflectsΣ (λ (v : Val n) → ⌞ ⟦ ψ ⟧ v ⌟) (cnf-sat? ψ)
reflects-cnf-sat {n = zero}   []     =
  ofʲ _ oh
reflects-cnf-sat {n = zero}  (ϕ ∷ ψ) =
  ofⁿ λ v vs → so-not (¬empty-clause-sat ϕ v) (and-so-l vs)
reflects-cnf-sat {n = suc n}  ψ      =
  DecΣ.elim
   {C = λ q → ReflectsΣ (λ (v : Val (suc n)) → ⌞ ⟦ ψ ⟧ v ⌟)
                        (Maybe.rec
                           ([ val-add (pos 0) , val-add (neg 0) ]ᵤ
                            <$> (    (cnf-sat? (unit-propagate (pos 0) ψ))
                                 <+> (cnf-sat? (unit-propagate (neg 0) ψ))))
                           (λ x → val-add x <$> cnf-sat? (unit-propagate x ψ))
                           ⌊ q ⌋m)}
   (λ x p → reflectsΣ-map
              (val-rem x)
              (unit-propagate-sat-add x ψ)
              (λ v → contra λ vs → unit-propagate-sat-rem x ψ v vs (unit-clause-sat x ψ p v vs))
              (reflects-cnf-sat (unit-propagate x ψ)))
   (λ ¬p → reflectsΣ-map
             (λ v → if v 0 then inl (val-rem (pos 0) v) else inr (val-rem (neg 0) v))
             (Sum.elim (unit-propagate-sat-add (pos 0) ψ) (unit-propagate-sat-add (neg 0) ψ))
             (λ v → contra λ vs →
                Bool.elim
                   {P = λ q → v 0 ＝ q →
                              [ So ∘ ⟦ unit-propagate (pos 0) ψ ⟧
                              , So ∘ ⟦ unit-propagate (neg 0) ψ ⟧
                              ]ᵤ (if q then inl (val-rem (pos fzero) v) else inr (val-rem (neg fzero) v))}
                   (λ e → unit-propagate-sat-rem (pos 0) ψ v vs (so≃is-true ⁻¹ $ e))
                   (λ e → unit-propagate-sat-rem (neg 0) ψ v vs (not-so (¬so≃is-false ⁻¹ $ e)))
                   (v 0) refl)
             (reflectsΣ-alter
                (reflects-cnf-sat (unit-propagate (pos 0) ψ))
                (reflects-cnf-sat (unit-propagate (neg 0) ψ))))
   (dec-has-unit-clause ψ)

dec-cnf-sat : (ψ : CNF n) → DecΣ λ (v : Val n) → ⌞ ⟦ ψ ⟧ v ⌟
dec-cnf-sat ψ .doesm  = cnf-sat? ψ
dec-cnf-sat ψ .proofm = reflects-cnf-sat ψ

