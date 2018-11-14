open import Data.Bool using (Bool; true; false; _∧_;_∨_; if_then_else_)
open import Data.Fin  as Fin using (Fin; zero; suc; fromℕ)
open import Data.List as L
open import Data.Maybe
open import Data.Nat
open import Data.Nat.Show as Show
open import Data.String renaming (_++_ to _s++_)
open import Data.Vec    renaming (_++_ to _v++_) hiding (head)
{- a label is used as a reference to a code segment - see more in Program -}
data Label : Set where
  s : ℕ -> Label
data NVar : Set where
  vN : String → NVar
data BVar : Set where
  vB : String → BVar
data ExpN : Set where
  nat  : ℕ    → ExpN   -- expression for ℕ
  nVar : NVar → ExpN   -- expression for natural variables, currently not
                       -- supported since no memory is implemented -- TODO

pExpN : ExpN → String
pExpN (nat x)       = Show.show x
pExpN (nVar (vN x)) = x
data ExpB : Set where
  bool : Bool → ExpB  -- expression for booleans
  bVar : BVar → ExpB  -- expression for boolean variables, currently not
                      -- supported since no memory is implemented -- TODO
data Exp : Set where
  expN : ExpN → Exp                          -- Wrapper for ExpN
  expB : ExpB → Exp                          -- Wrapper for ExpB
  _<?_ _<=?_ _>?_ _>=?_ : ExpN → ExpN → Exp  -- Might as well be constructors in
                                             -- ExpB
  _==n_ : ExpN → ExpN → Exp                  -- As above
  _==b_ : ExpB → ExpB → Exp                  -- As above
data Stm : Set where
  <_:=n_> : NVar → ℕ → Stm       -- Atomic assignment for natural variables
  <_:=b_> : BVar → ExpB → Stm    -- Atomic assignment for boolean variables
  -- wait : Exp → Stm            -- Awaits an expression to become true,
                                 -- currently not used
data Seg : Set where
  seg   : Label → Stm      → Seg       -- Regular segment, labels a statement
  block : Label → List Seg → Seg       -- Block, labels a list of segments
  par   : Label → List Seg → Seg       -- Parallel segment, labels a list of
                                       -- segments where each elements are run
                                       -- in parallel
  while : Label → ExpB → Seg → Seg  -- While loops segment
  if    : Label → ExpB → Seg → Seg  -- If statement segments
label : Seg → Label
label (seg x _)     = x
label (block x _)   = x
label (par x _)     = x
label (while x _ _) = x
label (if x _ _)    = x
record Prog : Set where
  constructor prog  -- Constructor used to make a program
  field
    main : Seg      -- The actual code of the program, should be a block segment
-- The extended LTL data type
data LTL : Set where
  T' ⊥         : LTL                            -- true & false
  ∼            : (φ : LTL) → LTL                -- not
  □ ◇          : (φ : LTL) → LTL                -- always & eventually
  _∧'_ _∨'_    : (φ : LTL) → LTL → LTL          -- and & or
  _⇒_          : (φ : LTL) → LTL → LTL          -- implies
  _~>_         : (φ : LTL) → (ψ : LTL) → LTL    -- leads to - (P ~> Q) ≡ □(P ⊂ ◇Q)
  at in' after : (l : Label) → LTL              -- at, in & after a code segment - extended
                                                -- from Owiki & Lamport
  _==n_        : (x : NVar) → (n : ℕ) → LTL     -- Nat variable x has the value n
  _==b_        : (x : BVar) → (y : BVar) → LTL  -- Bool variable x has the value of y
  isTrue       : (x : BVar) → LTL               -- Variable x has the value -- true

pLTL : LTL → String
pLTL T' = "T'"
pLTL ⊥ = "⊥"
pLTL (∼ x) = "(∼ " s++ (pLTL x) s++ ")"
pLTL (□ x) = "(□ " s++ (pLTL x) s++ ")"
pLTL (◇ x) = "(◇ " s++ (pLTL x) s++ ")"
pLTL (x ∧' x₁) = "(" s++ (pLTL x) s++ " ∧' " s++ (pLTL x₁) s++ ")"
pLTL (x ∨' x₁) = "(" s++ (pLTL x) s++ " ∨' " s++ (pLTL x₁) s++ ")"
pLTL (x ⇒ x₁) = "(" s++ (pLTL x) s++ " ⇒ " s++ (pLTL x₁) s++ ")"
pLTL (x ~> x₁) = "(" s++ (pLTL x) s++ " ~≳ " s++ (pLTL x₁) s++ ")"
pLTL (x ==n y) = "(" s++ pExpN (nVar x) s++ " == " s++ (Show.show y) s++ ")"
pLTL (vB x ==b vB y) = "(" s++ x s++ " == " s++ y s++ ")"
pLTL (at (s x)) = "(at " s++ (Show.show x) s++ ")"
pLTL (in' (s x)) = "(in " s++ (Show.show x) s++ ")"
pLTL (after (s x)) = "(after " s++ (Show.show x) s++ ")"
pLTL (isTrue (vB x)) = "(isTrue " s++ x s++ ")"
-- TODO this is already in the Standard-library
_=='_ : ℕ → ℕ → Bool
0 ==' 0 = true
0 ==' (suc y) = false
suc x ==' 0 = false
suc x ==' suc y = x ==' y
isEq : (φ : LTL) → (ψ : LTL) → Bool
isEq T' T' = true
isEq ⊥ ⊥   = true
isEq (∼ x) (∼ y) = isEq x y
isEq (□ x) (□ y) = isEq x y
isEq (◇ x) (◇ y) = isEq x y
isEq (x₁ ∧' x₂) (y₁ ∧' y₂) = (isEq x₁ y₁) ∧ ((isEq x₂ y₂))
isEq (x₁ ∨' x₂) (y₁ ∨' y₂) = (isEq x₁ y₁) ∧ ((isEq x₂ y₂))
isEq (x₁ ⇒ x₂) (y₁ ⇒ y₂)   = (isEq x₁ y₁) ∧ ((isEq x₂ y₂))
isEq (x₁ ~> x₂) (y₁ ~> y₂) = (isEq x₁ y₁) ∧ ((isEq x₂ y₂))
isEq (at (s x)) (at (s y)) = x ==' y
isEq (after (s x)) (after (s y)) = x ==' y
isEq (vN x ==n n₁) (vN y ==n n₂) = (x == y) ∧ (n₁ ==' n₂)
isEq (vB x ==b vB x₁) (vB x₂ ==b vB x₃) = (x == x₂) ∧ (x₁ == x₃)
isEq (isTrue (vB x)) (isTrue (vB y))    = x == y
isEq _ _ = false
data LTLRule : Set where
  ∧-e₁   : LTL → LTLRule        -- and-elimination on first element
  ∧-e₂   : LTL → LTLRule        -- and-elimination on second element
  ∧-i    : LTL → LTL → LTLRule  -- and-insertion on two LTL formulae
  ∨-i₁   : LTL → LTL → LTLRule  -- or-elimination on first element
  ∨-i₂   : LTL → LTL → LTLRule  -- or-elimination on second element
  ∨-e    : LTL → LTLRule
  □-e    : LTL → LTLRule
  □-∧-e₁ : LTL → LTLRule
  □-∧-e₂ : LTL → LTLRule
  exp-∧  : LTL → LTLRule
data Seq : ℕ → Set where
  ∅ : Seq zero
  _⋆_ : {n : ℕ} → Seq n → LTL → Seq (suc n)
data _⊨_ : {n : ℕ} → (σ : Seq n) → (φ : LTL) → Set where
  var   : ∀{n} {σ : Seq n} {ψ} → (σ ⋆ ψ) ⊨ ψ
  weak  : ∀{n} {σ : Seq n} {φ ψ} → σ ⊨ ψ → (σ ⋆ φ) ⊨ ψ
  T-i   : ∀{n} {σ : Seq n} → σ ⊨ T'
  ⊥-e   : ∀{n} {σ : Seq n} {ψ} → σ ⊨ ⊥ → σ ⊨ ψ
  ∼-i   : ∀{n} {σ : Seq n} {φ} → (σ ⋆ φ) ⊨ ⊥ → σ ⊨ (∼ φ)
  ∼-e   : ∀{n} {σ : Seq n} {φ} → σ ⊨ φ → σ ⊨ (∼ φ) → σ ⊨ ⊥
  ⇒-i   : ∀{n} {σ : Seq n} {φ ψ} → (σ ⋆ φ) ⊨ ψ → σ ⊨ (φ ⇒ ψ)
  ⇒-e   : ∀{n} {σ : Seq n} {φ ψ} → σ ⊨ (φ ⇒ ψ) → σ ⊨ φ → σ ⊨ ψ
  ∧'-i  : ∀{n} {σ : Seq n} {φ ψ} → σ ⊨ φ → σ ⊨ ψ → σ ⊨ (φ ∧' ψ)
  ∧'-e₁ : ∀{n} {σ : Seq n} {φ ψ} → σ ⊨ (φ ∧' ψ) → σ ⊨ φ
  ∧'-e₂ : ∀{n} {σ : Seq n} {φ ψ} → σ ⊨ (φ ∧' ψ) → σ ⊨ ψ
  ∨'-i₁ : ∀{n} {σ : Seq n} {φ ψ} → σ ⊨ φ → σ ⊨ (φ ∨' ψ)
  ∨'-i₂ : ∀{n} {σ : Seq n} {φ ψ} → σ ⊨ ψ → σ ⊨ (φ ∨' ψ)
  ∨'-e  : ∀{n} {σ : Seq n} {φ ψ χ} → σ ⊨ (φ ∨' ψ) → (σ ⋆ φ) ⊨ χ → (σ ⋆ ψ) ⊨ χ → σ ⊨ χ
  lem   : ∀{n} {σ : Seq n} {φ} → σ ⊨ (φ ∨' (∼ φ))

  -- extended with LTL
  init→◇   : ∀{n} {σ : Seq n} {φ} → σ ⊨ φ → σ ⊨ (◇ φ)
  □-e      : ∀{n} {σ : Seq n} {φ} → σ ⊨ □ φ → σ ⊨ φ
  □→◇      : ∀{n} {σ : Seq n} {φ} → σ ⊨ (□ φ) → σ ⊨ ◇ φ
  ∼□       : ∀{n} {σ : Seq n} {φ} → σ ⊨ (∼ (□ φ)) → σ ⊨ ◇ (∼ φ)
  ∼◇       : ∀{n} {σ : Seq n} {φ} → σ ⊨ (∼ (◇ φ)) → σ ⊨ (□ (∼ φ))
  ◇-i      : ∀{n} {σ : Seq n} {φ} → σ ⊨ φ → σ ⊨ ◇ φ
  ◇-∧'-e₁  : ∀{n} {σ : Seq n} {φ ψ} → σ ⊨ ◇ (φ ∧' ψ) → σ ⊨ ◇ φ
  ◇-∧'-e₂  : ∀{n} {σ : Seq n} {φ ψ} → σ ⊨ ◇ (φ ∧' ψ) → σ ⊨ ◇ ψ
  □-∧'-i   : ∀{n} {σ : Seq n} {φ ψ} → σ ⊨ □ φ → σ ⊨ □ ψ → σ ⊨ □ (φ ∧' ψ)
  □-∧'-e₁  : ∀{n} {σ : Seq n} {φ ψ} → σ ⊨ □ (φ ∧' ψ) → σ ⊨ □ φ
  □-∧'-e₂  : ∀{n} {σ : Seq n} {φ ψ} → σ ⊨ □ (φ ∧' ψ) → σ ⊨ □ ψ
  □→∼>     : ∀{n} {σ : Seq n} {φ ψ} → σ ⊨ □ (φ ⇒ (◇ ψ)) → σ ⊨ (φ ~> (◇ ψ))
  ~>→□     : ∀{n} {σ : Seq n} {φ ψ} → σ ⊨ (φ ~> (◇ ψ)) → σ ⊨ □ (φ ⇒ (◇ ψ))
test : ∀{n} {σ : Seq n} {φ} → (σ ⋆ φ) ⊨ ⊥ → σ ⊨ (∼ φ)
test p = ∼-i p

∧'-comm : {φ ψ : LTL} {n : ℕ} {σ : Seq n} → σ ⊨ (φ ∧' ψ) → σ ⊨ (ψ ∧' φ)
∧'-comm p = ∧'-i (∧'-e₂ p) (∧'-e₁ p)

∨'-comm : {φ ψ : LTL} {n : ℕ} {σ : Seq n} → σ ⊨ (φ ∨' ψ) → σ ⊨ (ψ ∨' φ)
∨'-comm p = ∨'-e p (∨'-i₂ var) (∨'-i₁ var)

∧'→∨' : {φ ψ : LTL} {n : ℕ} {σ : Seq n} → σ ⊨ (φ ∧' ψ) → σ ⊨ (φ ∨' ψ)
∧'→∨' p = ∨'-i₁ (∧'-e₁ p)

□-∧'-split₁ : {φ ψ : LTL} {n : ℕ} {σ : Seq n} → σ ⊨ □ (φ ∧' ψ) → σ ⊨ ((□ φ) ∧' (□ ψ))
□-∧'-split₁ p = ∧'-i (□-∧'-e₁ p) (□-∧'-e₂ p)

□-∧'-split₂ : {φ ψ : LTL} {n : ℕ} {σ : Seq n} → σ ⊨ ((□ φ) ∧' (□ ψ)) → σ ⊨ □ (φ ∧' ψ)
□-∧'-split₂ p = □-∧'-i (∧'-e₁ p) (∧'-e₂ p)

□-∧'-comm : {φ ψ : LTL} {n : ℕ} {σ : Seq n} → σ ⊨ □ (φ ∧' ψ) → σ ⊨ □ (ψ ∧' φ)
□-∧'-comm p = □-∧'-i (□-∧'-e₂ p) (□-∧'-e₁ p)

◇-∧'-split : {φ ψ : LTL} {n : ℕ} {σ : Seq n} → σ ⊨ ◇ (φ ∧' ψ) → σ ⊨ ((◇ φ) ∧' (◇ ψ))
◇-∧'-split p = ∧'-i (◇-∧'-e₁ p) (◇-∧'-e₂ p)

exLTL : ∀ {n}{σ : Seq n}{φ} → σ ⊨ φ → LTL
exLTL {φ = φ} p = φ

⇒-trans : {φ ψ χ : LTL} {n : ℕ} {σ : Seq n} → σ ⊨ (φ ⇒ ψ) → σ ⊨ (ψ ⇒ χ) → σ ⊨ (φ ⇒ χ)
⇒-trans p q =
  ⇒-i
    (⇒-e
      (weak q)
      (⇒-e
        (weak p)
        var))
-- Representation of propositional logic
-- data Props : Set where
--   T ⊥         : Props
--   _∧_ _∨_ _⇒_ : Props → Props → Props
--   p'          : ℕ → Props
--   ~_          : Props → Props
module Translator where
data Action : Set where
  assign : Action  -- Assignment
  seq    : Action  -- Progress into block segment (see Program)
  par    : Action  -- Progress into a parallel segment (see Program)
                   --TODO: change to co_oc
  while  : Action  -- Progress into a while loop (see Program)
  or'    : Action  -- Progress into an if statement (see Program)??
  inInf  : Action  -- TODO??
  flowA  : Action  -- Progress between segments
isEqA : Action → Action → Bool
isEqA assign assign = true
isEqA par par       = true
isEqA seq seq       = true
isEqA while while   = true
isEqA or' or'       = true
isEqA inInf inInf   = true
isEqA flowA flowA   = true
isEqA _ _           = false
data TransRel : Set where
  <_>_<_> : (c₁ : LTL) → Action → (c₂ : LTL) → TransRel  -- Hoare-style Triple
transStm : Label → Stm → TransRel
transStm l < (vN x) :=n n > = < (at l) > assign < ((after l) ∧' (vN x ==n n)) >
transStm l < x :=b bool b > = < (at l) > assign < (after l) ∧' (if b then (isTrue x) else ∼ (isTrue x)) > -- TODO: ??
transStm l < x :=b bVar y > = < (at l) > assign < (after l) ∧' (x ==b y) >
extractLabels : List Seg → LTL
extractLabels [] = ⊥
extractLabels (se ∷ [])   = at (label se)
extractLabels (se ∷ segs) = (at (label se)) ∧' extractLabels segs
head : {A : Set} → List A → Maybe A -- TODO :this can be found in the standard-library
head []       = nothing
head (x ∷ xs) = just x
flatten : {A : Set} → List (List A) → List A
flatten xs = L.foldl (λ x xs₁ → x L.++ xs₁) [] xs
seqFlow : Label → List Seg → List TransRel
seqFlow p [] = []
seqFlow p (x ∷ []) = < after (label x) > flowA < after p > ∷ []
seqFlow p (x ∷ (y ∷ xs)) = < after (label x) > flowA < at (label y) > ∷ (seqFlow p (y ∷ xs))
parFlow : List Seg → LTL
parFlow [] = ⊥
parFlow (x ∷ []) = after (label x)
parFlow (x ∷ xs) = (after (label x)) ∧' (parFlow xs)
{-# TERMINATING #-} -- used to guarantee that there is no infinite looping
transFlow : Seg → List TransRel
transFlow (seg _ _) = []
  -- If passed a simple segment (see Program), return empty
transFlow (block se segs) = seqFlow se segs L.++ L.foldl (λ rels se → rels L.++ transFlow se) [] segs
  -- If passed a block segment (see Program), return translation of the block
transFlow (par se segs) = < parFlow segs > flowA < after se > ∷ L.foldl (λ rels se → rels L.++ transFlow se) [] segs
  -- If passed a parallel segment (see Program), return translation of the par
transFlow (while l _ se) = < (after (label se)) > flowA < (at l) > ∷ transFlow se
  -- If passed a while segment (see Program), return translation of the while
transFlow (if l b se) = < (after (label se)) > flowA < (after l) > ∷ (transFlow se)
  -- If passed an if segment (see Program), return translation of the if
{-# TERMINATING #-} -- used to guarantee that there is no infinite looping
translate' : Seg → List TransRel
translate' (seg x stm) = (transStm x stm) ∷ []
  -- If passed a normal segment, pass on to transStm and return result
translate' (block l xs) with head xs
... | just x = (< (at l) > seq < (at (label x)) > ∷ (L.foldl (λ ls se → (translate' se) L.++ ls) [] xs))
  -- If passed a block segment with the first element being a segment, return
  -- the translation of the segment and translate all other segments
... | _ = []
  -- Else return empty
translate' (par x xs) = < (at x) > par < (extractLabels xs) > ∷ flatten (L.map (λ x → translate' x) xs)
  -- If passed a parallel segment, flatten the map with translate'
translate' (while l (bool x) se) = bCheck ∷ (translate' se)
  where bCheck = if x then < (at l) > while < (□ (in' (label se))) > else < (at l) > while < (after (label se)) >
  -- Check the boolean expression (see Program) of the while loop (see Program)
  -- and translate accordingly
translate' (while l (bVar (vB x)) se) = enterWhile ∷ exitWhile ∷ bVarCheck ∷ translate' se
  where bVarCheck = < at l > while < ((at (label se) ∧' isTrue (vB x)) ∨' ((after l) ∧' (∼ (isTrue (vB x))))) >
        exitWhile = < ((at l) ∧' □ (∼ (isTrue (vB x)))) > while < (after l) ∧' (□ (∼ (isTrue (vB x)))) >
        enterWhile = < ((at l) ∧' (□ (isTrue (vB x)))) > while < (□ (in' (label se))) >
  -- As above, but with a boolean variable
translate' (if x exp se) = translate' se
  -- Translate the if statement
translate : Prog → List TransRel
translate (prog main) = translate' main L.++ (transFlow main) -- Pass on to
module Rules where
data ProgRule : LTL → Action → Set where
  assRule   : (φ : LTL) → ProgRule φ assign  -- Assignment rule
  parRule   : (φ : LTL) → ProgRule φ par     -- Parallel rule
  seqRule   : (φ : LTL) → ProgRule φ seq     -- Sequential rule, used for
                                             -- entering non-basic segments (see
                                             -- Program)
  whileRule : (φ : LTL) → ProgRule φ while   -- While loop rule
  orRule    : (φ : LTL) → ProgRule φ or'     -- Or rule, used when making a
                                             -- branch
  inInf     : (φ : LTL) → ProgRule φ while   -- TODO
  atomLive  : (φ : LTL) → ProgRule φ flowA   -- Atomic liveness rule used to
                                             -- control progression
  exitRule  : (φ : LTL) → ProgRule φ while   -- Used when leaving a while loop
data Rule : Set where
  progR   : {a : Action } {φ : LTL} → ProgRule φ a → Rule  -- Program rule
  ltlR    : LTLRule → Rule                                 -- LTL rule
  customR : ℕ → LTL → LTL → Rule                           -- Custom rule
pRule : Rule → String
pRule (progR (assRule φ))    = "assRule"
pRule (progR (parRule φ))    = "parRule"
pRule (progR (seqRule φ))    = "seqRule"
pRule (progR (whileRule φ))  = "whileRule"
pRule (progR (orRule φ))     = "orRule"
pRule (progR (inInf φ))      = "inInf"
pRule (progR (atomLive φ))   = "atomLive"
pRule (progR (exitRule φ))   = "exitRule"
pRule (ltlR (∧-e₁ _))        = "∧-e₁"
pRule (ltlR (∧-e₂ _))        = "∧-e₂"
pRule (ltlR (∧-i _ _))       = "∧-i"
pRule (ltlR (∨-i₁ _ _))      = "∨-i₁"
pRule (ltlR (∨-i₂ _ _))      = "∨-i₂"
pRule (ltlR (exp-∧ _))       = "exp-∧"
pRule (ltlR (∨-e _))         = "∨-e"
pRule (ltlR (□-e _))         = "□-e"
pRule (ltlR (□-∧-e₁ _))      = "□-∧-e₁"
pRule (ltlR (□-∧-e₂ _))      = "□-∧-e₂"
pRule (customR x x₁ x₂)      = "Custom " s++ Show.show x
