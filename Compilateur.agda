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

{-
  b, e₁, e₂ ::=              (expressions)
              | v            (valeur)
              | plus e₁ e₂   (addition)
              | ifte b e₁ e₂ (conditionnelle)
-}

-- ex₁ = plus (val 1) (val 1)

-- ex₂ = plus (val 2) (ifte (val true)
--                          (val 3)
--                          (plus (val 1) (val 7)))


-- --------------------------------
-- Machine à pile
-- --------------------------------

{-
  π ::=                      (pile)
      | ε                    (pile vide)
      | v ∙ π                (valeur sur pile)
-}

{-
  c₁, c₂ ::=                 (machine à pile)
           | SKIP
           | PUSH v          (valeur sur pile)
           | ADD             (addition sur pile)
           | IFTE c₁ c₂      (conditionnelle sur pile)
           | c₁ # c₂         (séquence)
-}

-- ex₃ = PUSH 1 #
--       PUSH 1 #
--       ADD

-- ex₄ = PUSH 2 #
--       PUSH true #
--       IFTE (PUSH 3)
--            (PUSH 1 # PUSH 7 # ADD) #
--       ADD

-- --------------------------------
-- Compilateur
-- --------------------------------

