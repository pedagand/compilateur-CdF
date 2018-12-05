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

data valeur : Set where
  estNat  : (n : ℕ)    → valeur
  estBool : (b : Bool) → valeur

{-
  b, e₁, e₂ ::=              (expressions)
              | v            (valeur)
              | plus e₁ e₂   (addition)
              | ifte b e₁ e₂ (conditionnelle)
-}

data exp : Set where
  val  : (v : valeur)                  → exp
  plus : (e₁ : exp)(e₂ : exp)          → exp
  ifte : (b : exp)(e₁ : exp)(e₂ : exp) → exp

ex₁ : exp
ex₁ = plus (val (estNat 1)) (val (estNat 1))

ex₂ : exp
ex₂ = plus (val (estNat 2))
           (ifte (val (estBool true))
                 (val (estNat 3))
                 (plus (val (estNat 1)) (val (estNat 7))))

semE : exp → Option valeur
semE (val v)                          = OK v
semE (plus e₁ e₂)
  with semE e₁ | semE e₂
... | OK (estNat n₁) | OK (estNat n₂) = OK (estNat (n₁ + n₂))
... | OK (estBool b) | _              = KO
... | OK (estNat n₁) | OK (estBool b) = KO
... | OK v           | KO             = KO
... | KO             | _              = KO
semE (ifte b e₁ e₂)
  with semE b | semE e₁ | semE e₂
... | OK (estBool v) | v₁ | v₂        = if v then v₁ else v₂
... | _ | _ | _                       = KO

test-ex₁ : semE ex₁ ≡ OK (estNat 2)
test-ex₁ = refl

-- "The above proposition is occasionally useful."
--         Whitehead & Russell (PM, vol.II, p.362)

test-ex₂ : semE ex₂ ≡ OK (estNat 5)
test-ex₂ = refl

-- --------------------------------
-- Machine à pile
-- --------------------------------

{-
  π ::=                      (pile)
      | ε                    (pile vide)
      | v ∙ π                (valeur sur pile)
-}

data pile : Set where
  ε   :                          pile
  _∙_ : (v : valeur)(π : pile) → pile

infixr 5 _∙_

{-
  c₁, c₂ ::=                 (machine à pile)
           | SKIP
           | PUSH v          (valeur sur pile)
           | ADD             (addition sur pile)
           | IFTE c₁ c₂      (conditionnelle sur pile)
           | c₁ # c₂         (séquence)
-}

data code : Set where
  SKIP :                          code
  PUSH : (v : valeur)           → code
  ADD  :                          code
  IFTE : (c₁ : code)(c₂ : code) → code
  _#_  : (c₁ : code)(c₂ : code) → code

infixr 20 _#_

ex₃ : code
ex₃ = PUSH (estNat 1) #
      PUSH (estNat 1) #
      ADD

ex₄ : code
ex₄ = PUSH (estNat 2) #
      PUSH (estBool true) #
      IFTE (PUSH (estNat 3))
           (PUSH (estNat 1) # PUSH (estNat 7) # ADD) #
      ADD

-- --------------------------------
-- Compilateur
-- --------------------------------

compile : exp → code
compile (val v)        = PUSH v
compile (plus e₁ e₂)   = compile e₂ #
                         compile e₁ #
                         ADD
compile (ifte b e₁ e₂) = compile b #
                         IFTE (compile e₁)
                              (compile e₂)
