-- open import Data.Bool

data Bool : Set where
  true false : Bool

{-
{-# BUILTIN BOOL  Bool  #-}
{-# BUILTIN FALSE False #-}
{-# BUILTIN TRUE  True  #-}
-}

infixr 6 _∧_

_∧_ : Bool → Bool → Bool
true  ∧ b = b
false ∧ b = false

if_then_else_ : ∀ {A : Set} → Bool → A → A → A
if true  then t else f = t
if false then t else f = f

-- open import Data.Nat

data ℕ : Set where
  zero : ℕ
  suc  : (n : ℕ) → ℕ

{-# BUILTIN NATURAL ℕ #-}

_≟ℕ_ : ℕ → ℕ → Bool
zero ≟ℕ zero = true
zero ≟ℕ suc y = false
suc x ≟ℕ zero = false
suc x ≟ℕ suc y = x ≟ℕ y

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

-- open import Data.List

infixr 5 _∷_
data List (A : Set) : Set where
  []  : List A
  _∷_ : (T : A)(Γ : List A) → List A

{-# BUILTIN LIST List #-}

-- open import Data.Maybe

data Option (A : Set) : Set where
  OK : (x : A) → Option A
  KO : Option A


record RawMonad (M : Set → Set) : Set₁ where
  infixl 1 _>>=_ _>>_

  field
    return : ∀ {A} → A → M A
    _>>=_  : ∀ {A B} → M A → (A → M B) → M B

  _>>_ : ∀ {A B} → M A → M B → M B
  m₁ >> m₂ = m₁ >>= λ _ → m₂


record RawMonadZero (M : Set → Set) : Set₁ where
  field
    monad : RawMonad M
    ∅     : ∀{A} → M A

  open RawMonad monad public



maybe : ∀ {A : Set} {B : Option A → Set} →
        ((x : A) → B (OK x)) → B KO → (x : Option A) → B x
maybe j n (OK x) = j x
maybe j n KO  = n

monad : RawMonad Option
monad = record
  { return = OK
  ; _>>=_ = λ m f → maybe f KO m }

monadZero : RawMonadZero Option
monadZero = record
  { monad = monad
  ; ∅     = KO
  }

open RawMonadZero monadZero hiding (monad) public

-- open import Data.Unit

record ⊤ : Set where
  instance constructor tt

{- {-# BUILTIN UNIT ⊤ #-} -}

--

-- open import Relation.Binary.PropositionalEquality

infix 4 _≡_
data _≡_ {A : Set} (x : A) : A → Set where
  instance refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}

subst : ∀ {A : Set} (P : A → Set)
         {x₁ x₂} → x₁ ≡ x₂ → P x₁ → P x₂
subst P refl p = p

cong : ∀ {A : Set} {B : Set}
       (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl

-- open import Data.Empty

data ⊥ : Set where


-- open import Relation.Nullary

infix 3 ¬_

¬_ : Set → Set
¬ P = P → ⊥

data Dec (P : Set) : Set where
  yes : ( p :   P) → Dec P
  no  : (¬p : ¬ P) → Dec P


-- open import Relation.Binary

REL : Set → Set → Set₁
REL A B = A → B → Set

Decidable : {A : Set} {B : Set} → REL A B → Set
Decidable _∼_ = ∀ x y → Dec (x ∼ y)

-- open import Data.Product

infixr 4 _,_

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ public

infix 2 Σ-syntax

Σ-syntax : ∀ (A : Set) → (A → Set) → Set
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B


-- open import Data.Maybe.Base

Is-OK : ∀ {A : Set} → Option A → Set
Is-OK (OK _) = ⊤
Is-OK KO  = ⊥

to-witness : ∀ {P : Set} (m : Option P) → Is-OK m → P
to-witness (OK p) _  = p
to-witness KO  ()
