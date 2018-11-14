{-# OPTIONS --without-K #-}
open import Agda.Primitive using ( Level ; lsuc; lzero; _⊔_ )
_ = Set
open import 2018-07-06-mini-hott hiding (Path)
module Base {ℓ} where

  record Graph : Type (lsuc ℓ) where
    constructor graph
    field
      -- G = (Node, Edge)
      Node : Type ℓ
      Edge : Node → Node → Type ℓ

      -- Properties
      -- ==========

      -- The vertices form a set.
      NodeIsSet : isSet Node

      -- No multi-graphs.
      EdgeIsProp : ∀ (x y : Node) → isProp (Edge x y)

      -- Undirected.
      Undirected : ∀ (x y : Node) → Edge x y → Edge y x

  open Graph public
-- .
-- data G4 : Type ℓ where
--   v₁ v₂ v₃ v₄ : G4
--
-- e : G4 → G4 → Type ℓ
-- e v₁ v₂ = v₁ == v₂
-- e v₁ x₃ = v₁ == v₃
-- e v₂ x₃ = v₂ == v₃
-- e v₂ x₄ = v₂ == v₄
-- e v₂ v₁ = v₂ == v₁
-- e x₃ v₁ = v₃ == v₁
-- e x₃ v₂ = v₃ == v₂
-- e x₄ v₂ = v₄ == v₂
--
-- Example : Graph
-- Node Example = G4
-- Edge Example = e
-- NodeIsSet Example = λ u v → λ { idp q → {!   !}}
-- EdgeIsProp Example = λ u v → {!   !}
-- Undirected Example = {!   !}
module Lemmas {ℓ} where
  open Base {ℓ}
  -- Lem.
  lem₀'
    : ∀ {G H : Graph}
    → Σ (Node G == Node H) (λ α →
        Σ (tr (λ X → (X → X → Type ℓ)) α (Edge G) == Edge H) (λ β →
          (tr isSet α (NodeIsSet G) == NodeIsSet H)
        × (tr₂
            (Type ℓ)
            (λ X → X → X → Type ℓ)
            (λ X R → (x y : X) → isProp (R x y))
            α
            β
            (EdgeIsProp G) == (EdgeIsProp H)
        × (tr₂
            (Type ℓ)
            (λ X  → X → X → Type ℓ)
            (λ X R → (x y : X) →  R x y → R y x))
            α
            β
            (Undirected G) == (Undirected H))))
    ≃ G == H

  lem₀' = qinv-≃
    ( λ {(idp , (idp , (idp , (idp , idp)))) → idp })     -- Fun. Equiv.
    ((λ {idp → idp , idp , (idp , (idp , idp))})          -- Fun. Inverse
      , (λ {idp →  idp})                                  -- Homotopy
      , λ { (idp , (idp , (idp , (idp , idp))))  →  idp}  -- Homotopy
    )
  -- Lem.
  lem₁'
    : ∀ {G H : Graph}
    → Σ (Node G == Node H) (λ α →
        (tr (λ X → (X → X → Type ℓ)) α (Edge G) == Edge H))
    ≃  Σ ((Node G == Node H)) (λ α →
        Σ (tr (λ X → (X → X → Type ℓ)) α (Edge G) == Edge H) λ β
        → (tr isSet α (NodeIsSet G) == NodeIsSet H)
        × (tr₂ (Type ℓ)
            (λ X  → X → X → Type ℓ)
            (λ X R → (x y : X) → isProp (R x y))
             α β (EdgeIsProp G) == (EdgeIsProp H)
        × (tr₂ (Type ℓ)
         (λ X  → X → X → Type ℓ)
         (λ X R → (x y : X) →  R x y → R y x))
          α β (Undirected G) == (Undirected H)))

  lem₁' {G}{H} = qinv-≃
    (λ { (α , β) →   -- Fun. Equiv.
      (α
        , (β
          , (set-is-prop-always _ _)
          , (pi-is-prop (λ x → pi-is-prop λ x → prop-is-prop-always) _ _)
          , pi-is-prop ((λ x → pi-is-prop λ x → pi-is-prop λ x → EdgeIsProp H _ _)) _ _))})

      ((λ {(α , (β , _)) → α , β})
        , (λ {(α , (β , _))
          → pair= (idp
              , pair= (idp
                , ispropA×B
                  (prop→set
                    (pi-is-prop λ a → pi-is-prop λ x → prop-is-prop-always)
                    _
                    _)
                  (ispropA×B
                    (prop→set
                      (pi-is-prop
                        (λ x → pi-is-prop
                          (λ a → prop-is-prop-always)
                        )
                      )
                      _ -- EdgeIsProp H
                      _
                      )
                    (prop→set
                      (pi-is-prop
                        (λ a → pi-is-prop λ b → pi-is-prop λ e → EdgeIsProp H _ _)) _ _)) _ _)) })
        , (λ {(α , β) → idp} ))
  -- LemAux:
  lemAux
    : ∀ {G H : Graph}
    → (α : Node G == Node H)
    → (tr (λ X → (X → X → Type ℓ)) α (Edge G) == Edge H)
      ≃
      (∀ (x y : Node G)
          → Edge G x y == Edge H (coe α x) (coe α y))
  lemAux {G}{H} idp = qinv-≃
    f ( g , -- g
      H₁
      , H₂)
    where
      f : tr (λ X → (X → X → Type ℓ)) idp (Edge G) == Edge H
        → (∀ x y → Edge G x y == Edge H (coe idp x) (coe idp y))
      f idp x y = idp

      g : (∀ x y → Edge G x y == Edge H (coe idp x) (coe idp y))
        → tr (λ X → (X → X → Type ℓ)) idp (Edge G) == Edge H
      g k = funext (λ x → funext λ y → k x y)

      H₁ : f ∘ g ∼ id
      H₁ k = {!   !}

      H₂ : g ∘ f ∼ id
      H₂ idp = {! (g ∘ f) idp == id idp  !}


  -- Lem.
  lem₂'
    : ∀ {G H : Graph}
    → -- A :
      Σ (Node G == Node H) (λ α →
        (tr (λ X → (X → X → Type ℓ)) α (Edge G) == Edge H))
    ≃ -- B:
      Σ (Node G == Node H) (λ α →
        (∀ (x y : Node G)
            → Edge G x y == Edge H (coe α x) (coe α y)))

  lem₂' {G}{H} = qinv-≃
    -- f : A → B
    (λ { (idp , idp) → idp  , λ x y → happly (happly idp y) x }) -- or just idp?
    -- g : B → A
    ((λ {(idp , k) → (idp , funext (λ x → funext (λ y → k x y)) )})
      ,  -- f ∘ g ∼ id_B
        (λ { (idp , y) → pair= ({!   !} , {!   !}) })
      , -- g ∘ f ∼ id_A
      λ { (idp , idp) → pair= (idp , {!  !}) })
  -- Lem.
  lem₀
    : ∀ {G H : Graph}
    → (α : Node G == Node H)
    → (β : tr (λ X → (X → X → Type ℓ)) α (Edge G) == Edge H)
    → (tr isSet α (NodeIsSet G) == NodeIsSet H)
    → tr₂ (Type ℓ)
          (λ X  → X → X → Type ℓ)
          (λ X R → (x y : X) → isProp (R x y))
           α β (EdgeIsProp G) == (EdgeIsProp H)
    → tr₂ (Type ℓ)
       (λ X  → X → X → Type ℓ)
       (λ X R → (x y : X) →  R x y → R y x)
        α β (Undirected G) == (Undirected H)
    →  G == H

  lem₀ idp idp idp idp idp = idp
  -- Lem.
  lem₁
    : ∀ { G H : Graph}
    → (α : Node G == Node H)
    → (β : tr (λ X → (X → X → Type ℓ)) α (Edge G) == Edge H)
    →  G == H

  lem₁ {G}{H} α β = lem₀ α β
    (set-is-prop-always _ _)
    (pi-is-prop (λ x → pi-is-prop λ x → prop-is-prop-always) _ _) -- EdgeIsProp
    (pi-is-prop (λ x → pi-is-prop λ x → pi-is-prop λ x → EdgeIsProp H _ _) _ _) -- Undirected case
  -- Lem.
  lem₂
    : ∀ {G H : Graph}
    → (α : Node G == Node H)
    → (β :  ∀ x y → Edge G x y == Edge H (coe α x) (coe α y))
    →  G == H

  lem₂ idp β = lem₁ idp (funext (λ x → funext (λ y → β x y)))
  -- Lem.
  lem₃
    : ∀ { G H : Graph}
    → (α : Node G == Node H)
    → (β :  ∀ x y → Edge G x y ⇔ Edge H (coe α x) (coe α y))
    →  G == H

  lem₃ {G}{H} α β = lem₂ α λ x y → ispropA-B (EdgeIsProp G _ _) (EdgeIsProp H _ _) (β x y)
  -- Lem.
  lem₄
    : ∀ { G H : Graph}
    → (α : Node G ≃ Node H)
    → (β :  ∀ x y → Edge G x y ⇔ Edge H ((α ∙) x) ((α ∙) y))
    →  G == H

  lem₄ {G}{H} α β = lem₃ (ua α) (λ x y
      → tr₂ (Node H)
            (λ X → Node H)
            (λ n m → Edge G x y ⇔ Edge H n m)
            (! (ua-coe α x))
            (transport-const (! (ua-coe α x)) _ · ! ua-coe α y)
           (β x y))
open Lemmas
module Isomorphism {ℓ} where

  open Base {ℓ}

  _≃Iso_ : Graph → Graph → Type ℓ
  G ≃Iso H =
    Σ (Node G ≃ Node H)
      (λ α → (x y : Node G)                        -- α
       → Edge G x y ⇔ Edge H ((α ∙) x) ((α ∙) y))  -- β

  -- Remarks: Edge is propositional.
  -- Agda Question:
  -- What to remove these parenthesis (α ∙)
  -- Thm.
  A≃IsoA
    : ∀ {A : Graph }
    ----------
    → A ≃Iso A

  A≃IsoA {A} = ( idEqv , λ x y → fun id , fun id )
  -- Thm.
  thm
    : ∀ {G H : Graph}
    ------------------------
    → (G == H) ≃ (G ≃Iso H)

  thm {G}{H} = qinv-≃ f (g , H₁ , H₂)
    where
      f : G == H → G ≃Iso H
      f p = tr (λ X → G ≃Iso X) p (A≃IsoA {A = G})

      g : G ≃Iso H → G == H
      g (α , β) =  lem₄ α β

      H₁ : f ∘ g ∼ id
      H₁ (α , β) = {!   !}

      H₂ : g ∘ f ∼ id
      H₂ idp = {! (g ∘ f) idp  !}

module Walks {ℓ}
  {G : Base.Graph {ℓ}}
  where

  open Base {ℓ}

  -- Def.
  data Walk : Node G → Node G → Type ℓ where

    ⟨_⟩
      : ∀ {x : Node G}
      → Walk x x

    _⊙_
      : ∀ { x y z : Node G}
      → Walk x y → Edge G y z
      ------------------------
      → Walk x z

  -- Syntax.
  syntax Walk x y = x ⇢ y
module Connected {ℓ} {G : Base.Graph {ℓ}} where

  open Base {ℓ}
  open Walks {ℓ}
  -- Pred.
  Connected : (G : Graph) → Type ℓ
  Connected G = ∀ {x y : Node G} → Walk {G} x y

  ConnectedGraph : Type (lsuc ℓ)
  ConnectedGraph = Σ Graph Connected
module RotationSystem {ℓ}
  {G : Base.Graph {ℓ}}
  where

  open Base {ℓ}
  open Walks {ℓ}
  -- Def.
  Star
    : Node G
    --------
    → Type ℓ

  Star = λ (x : Node G) → Σ (Node G) (λ y → Edge G y x)
  -- -- Relation.
  -- postulate
  --   StarRelation : ∀ {x : Node G} → Star x → Star x → Star x → Type ℓ
  --
  -- postulate
  --   StarRelationIsProp : ∀ {x : Node G} {a b c : Star x} → isProp (StarRelation a b c)
  -- Each node has incident nodes.
module CyclicForm {ℓᵢ ℓⱼ} where

  record Cyclic (A : Type ℓᵢ)             -- Carrier
                (R : A → A → A → Type ℓⱼ) -- Clockwise
                : Type (ℓᵢ ⊔ ℓⱼ) where
    field

      RisProp : ∀ {a b c : A} → isProp (R a b c)

      axiom₀
        : ∀ {a b c : A}
        → R a b c
        → R a c b
        ---------
        → b == c

      axiom₁
        : ∀ {a b : A}
        -------------
        → R a b b

      axiom₂
        : ∀ {a b c : A}
        → R a b c
        ---------
        → R b c a

      axiom₃
        : ∀ {a b c d : A}
        → R a b c
        → R a c d
        ---------
        → R a b d

      axiomₓ
        : ∀ {a b c : A} → ∥ (R a b c) + (R a c b) ∥
  -- Def.
  CyclicIsProp : ∀ {A}{R} → isProp (Cyclic A R)
  CyclicIsProp x y = {!   !}

  -- ∀ {x : Node G} → Cyclic (Star x) (StarRelation {x})
