open import Lib

-- ================================================================
-- Types dépendants : tout un programme !
--
-- Séminaire du 28 Nov. 2018
-- Pierre-Évariste Dagand -- Sorbonne Université - CNRS - Inria
-- https://bit.ly/2QqmiNC
-- https://www.lip6.fr/Pierre-Evariste.Dagand/stuffs/college-2018/seminaire.zip
-- ================================================================

-- Inspiré de
--     "Correctness of a compiler for arithmetic expressions"
--         McCarthy, J. & Painter, J.A. (1967)

-- "This paper contains a proof of the correctness of a simple
-- compiling algorithm for compiling arithmetic expressions into
-- machine language."

-- "Note that there are no jump instructions. Needless to say, this is
-- a severe restriction on the generality of our results which we
-- shall overcome in future work."

-- --------------------------------
-- Expressions
-- --------------------------------

{-
  v ::=                      (valeurs)
      | true | false         (booléens)
      | 0 | 1 | ...          (entiers naturel)
-}

data type : Set where
   nat bool : type

variable T : type

valeur : type → Set
valeur nat  = ℕ
valeur bool = Bool

{-
  b, e₁, e₂ ::=              (expressions)
              | v            (valeur)
              | plus e₁ e₂   (addition)
              | ifte b e₁ e₂ (conditionnelle)
-}

data exp : type → Set where
  val  : (v : valeur T)                → exp T
  plus : (e₁ : exp nat)(e₂ : exp nat)  → exp nat
  ifte : (b : exp bool)(e₁ e₂ : exp T) → exp T

ex₁ : exp nat
ex₁ = plus (val 1) (val 1)

ex₂ : exp nat
ex₂ = plus (val 2)
           (ifte (val true)
                 (val 3)
                 (plus (val 1) (val 7)))

semE : exp T → valeur T
semE (val v)        = v
semE (plus e₁ e₂)   = semE e₁ + semE e₂
semE (ifte b e₁ e₂) = if semE b then semE e₁ else semE e₂

test-ex₁ : semE ex₁ ≡ 2
test-ex₁ = refl

-- "The above proposition is occasionally useful."
--         Whitehead & Russell (PM, vol.II, p.362)

test-ex₂ : semE ex₂ ≡ 5
test-ex₂ = refl

-- --------------------------------
-- Machine à pile
-- --------------------------------

{-
  π ::=                      (pile)
      | ε                    (pile vide)
      | v ∙ π                (valeur sur pile)
-}

type-pile : Set
type-pile = List type

variable σ σ₁ σ₂ σ₃ : type-pile

data pile : type-pile → Set where
  ε   : pile []
  _∙_ : valeur T → pile σ → pile (T ∷ σ)

infixr 5 _∙_

tete : pile (T ∷ σ) → valeur T
tete (t ∙ _) = t

queue : pile (T ∷ σ) → pile σ
queue (_ ∙ s) = s

{-
  c₁, c₂ ::=                 (machine à pile)
           | SKIP
           | PUSH v          (valeur sur pile)
           | ADD             (addition sur pile)
           | IFTE c₁ c₂      (conditionnelle sur pile)
           | c₁ # c₂         (séquence)
-}

data code : type-pile → type-pile → Set where
  SKIP :                                      code σ σ
  PUSH : (v : valeur T)                     → code σ (T ∷ σ)
  ADD  :                                      code (nat ∷ nat ∷ σ) (nat ∷ σ)
  IFTE : (c₁ c₂ : code σ₁ σ₂)               → code (bool ∷ σ₁) σ₂
  _#_  : (c₁ : code σ₁ σ₂)(c₂ : code σ₂ σ₃) → code σ₁ σ₃

infixr 20 _#_

ex₃ : code [] (nat ∷ [])
ex₃ = PUSH 1 #
      PUSH 1 #
      ADD

ex₄ : code [] (nat ∷ [])
ex₄ = PUSH 2 #
      PUSH true #
      IFTE (PUSH 3)
           (PUSH 1 # PUSH 7 # ADD) #
      ADD

semC : code σ₁ σ₂ → pile σ₁ → pile σ₂
semC SKIP π                   = π
semC (PUSH v) π               = v ∙ π
semC ADD (m ∙ n ∙ π)          = m + n ∙ π
semC (IFTE c₁ c₂) (true ∙ π)  = semC c₁ π
semC (IFTE c₁ c₂) (false ∙ π) = semC c₂ π
semC (c₁ # c₂) π              = semC c₂ (semC c₁ π)

-- --------------------------------
-- Compilateur
-- --------------------------------

compile : exp T → code σ (T ∷ σ)
compile (val v)        = PUSH v
compile (plus e₁ e₂)   = compile e₂ #
                         compile e₁ #
                         ADD
compile (ifte b e₁ e₂) = compile b #
                         IFTE (compile e₁)
                              (compile e₂)

correction : (e : exp T)(π : pile σ) → semC (compile e) π ≡ semE e ∙ π
correction (val v) π                  = refl
correction (plus e₁ e₂) π
  rewrite correction e₂ π
        | correction e₁ (semE e₂ ∙ π) = refl
correction (ifte b e₁ e₂) π
  rewrite correction b π
  with semE b
... | true                            = correction e₁ π
... | false                           = correction e₂ π
