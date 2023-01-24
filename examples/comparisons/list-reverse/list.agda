open import Relation.Binary.PropositionalEquality

open ≡-Reasoning

-----------------
----[ LISTS ]----
-----------------

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

snoc : {A : Set} → List A → A → List A
snoc []      a = a ∷ []
snoc (x ∷ l) a = x ∷ snoc l a

reverse : {A : Set} → List A → List A
reverse []      = []
reverse (x ∷ l) = snoc (reverse l) x

------------------
----[ LEMMAS ]----
------------------

reverse-helper : {A : Set} → (x : A) → (l : List A) → reverse (snoc l x) ≡ x ∷ reverse l
reverse-helper x []      = refl
reverse-helper x (a ∷ l) = begin
    reverse (snoc (a ∷ l) x)
  ≡⟨⟩
    reverse (a ∷ snoc l x)
  ≡⟨⟩
    snoc (reverse (snoc l x)) a
  ≡⟨ cong (λ k → snoc k a) (reverse-helper x l) ⟩
    snoc (x ∷ reverse l) a
  ≡⟨⟩
    x ∷ reverse (a ∷ l)
  ∎

reverse-selfinverse : {A : Set} → (l : List A) → reverse (reverse l) ≡ l
reverse-selfinverse []      = refl
reverse-selfinverse (x ∷ l) = trans
    (reverse-helper x (reverse l))
    (cong (λ k → x ∷ k) (reverse-selfinverse l))
